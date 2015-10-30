import 'package:parsers/parsers.dart';
import 'dart:io';

// An error.
class Error implements Exception {
  String cause;
  Error(this.cause);
  String toString() => 'error in Zinc script: $cause';
}


// AST.
class Node {
  Obj interpret(ZincInterpreter interp) => null;
}

// Identifier.
class Id extends Node {
  final String id;
  Id(this.id);
  String toString() => 'Id($id)';
  Obj interpret(ZincInterpreter interp) => interp.getv(id);
}

// Integer literal.
class IntLiteral extends Node {
  final int value;
  IntLiteral(this.value);
  String toString() => 'IntLiteral($value)';
  Obj interpret(ZincInterpreter interp) => new IntObj(value);
}

// Any kind of operator.
class Anyop extends Node {
  void set(ZincInterpreter interp, OpFuncType func) {}
}

// Operator.
class Op extends Anyop {
  final String op;
  final bool orig;
  Op(this.op, [this.orig = false]);
  String toString() => 'Op($op, $orig)';
  OpFuncType get(ZincInterpreter interp) =>
    this.orig ? interp.op0[op] : interp.op1[op];
  void set(ZincInterpreter interp, OpFuncType func) { interp.op1[op] = func; }
}

// Unary operator (len).
class Lenop extends Anyop {
  final bool orig;
  Lenop([this.orig = false]);
  String toString() => 'Lenop($orig)';
  OpFuncType get(ZincInterpreter interp) =>
    this.orig ? interp.op0['#'] : interp.op1['#'];
  void set(ZincInterpreter interp, OpFuncType func) { interp.op1['#'] = func; }
}

// Magic operator.
class Magicop extends Anyop {
  final String op;
  Magicop(this.op);
  String toString() => 'Magicop($op)';
  Obj interpret_with(ZincInterpreter interp, Obj x, Obj y) {
    if (op == 'cut') {
      if (y is! IntObj) { throw new Error('cannot cut int with non-int'); }
      if (x is IntObj) {
        return new SetObj(x.value.toString().split(y.value.toString()).map(
          int.parse));
      } else {
        assert(x is SetObj);
        List<List<Obj>> res = [[]];
        for (Obj obj in x.vals(interp)) {
          if (obj == y) { res.add([]); }
          else { res.last.add(obj); }
        }
        return new SetObj(new List.from(res.map((l) =>
          l.length == 1 ? l[0] : new SetObj(l))));
      }
    } else if (op == 'join') {
      if (x is! SetObj) { throw new Error('can only join set'); }
      if (y is! IntObj) { throw new Error('can only join set with int'); }
      String res = '';
      for (Obj obj in x.vals(interp)) {
        if (obj is! IntObj) { throw new Error('joining set must contain ints'); }
        res += obj.value.toString();
      }
      return new IntObj(int.parse(res));
    }
  }
}

// Unary operator (len) expression.
class Len extends Node {
  final Lenop op;
  final Node value;
  Len(this.op, this.value);
  String toString() => 'Len($op, $value)';
  Obj interpret(ZincInterpreter interp) =>
    op.get(interp)(interp, value.interpret(interp), null);
}

// Binary operator expression.
class Binop extends Node {
  final Node lhs, rhs;
  final Op op;
  Binop(this.lhs, this.op, this.rhs);
  String toString() => 'Binop($lhs, $op, $rhs)';
  Obj interpret(ZincInterpreter interp) =>
    op.get(interp)(interp, lhs.interpret(interp), rhs.interpret(interp));
}

// Clause.
enum ClauseKind { Where, Sort }
class Clause extends Node {
  final ClauseKind kind;
  final Node expr;
  Clause(this.kind, this.expr);
  String toString() => 'Clause($kind, $expr)';
  Obj interpret_with(ZincInterpreter interp, SetObj set, Id id) {
    List<Obj> res = [];
    List<Obj> values = set.vals(interp);
    switch (kind) {
    case ClauseKind.Where:
      for (int i=0; i<values.length; i++) {
        Obj obj = values[i];
        interp.push_scope();
        interp.setv(id.id, obj);
        interp.setv('_', new IntObj(i));
        Obj x = expr.interpret(interp);
        interp.pop_scope();
        if (x is IntObj) {
          if (x.value != 0) { res.add(obj); }
        } else { throw new Error('where clause condition must be an integer'); }
      }
      break;
    case ClauseKind.Sort:
      res = values;
      res.sort((x, y) {
        interp.push_scope();
        interp.setv(id.id, x);
        Obj x_by = expr.interpret(interp);
        interp.setv(id.id, y);
        Obj y_by = expr.interpret(interp);
        interp.pop_scope();
        if (x_by is IntObj && y_by is IntObj) {
          return x_by.value.compareTo(y_by.value);
        } else { throw new Error('sort clause result must be an integer'); }
      });
      break;
    }
    return new SetObj(new List.from(res.reversed));
  }
}

// Set comprehension.
class SetComp extends Node {
  final Id id;
  final Node set;
  final Clause clause;
  SetComp(this.id, this.set, this.clause);
  String toString() => 'SetComp($id, $set, $clause)';
  Obj interpret(ZincInterpreter interp) {
    Obj setobj = set.interpret(interp);
    if (setobj is SetObj) {
      return clause.interpret_with(interp, setobj, id);
    } else { throw new Error('set comprehension rhs must be set type'); }
  }
}

// Operator rewrite.
class OpRewrite extends Node {
  final Anyop op;
  final Node value;
  final Id lid, rid; // Can be null!
  OpRewrite(this.op, this.value, [this.lid, this.rid]);
  String toString() => 'OpRewrite($lid, $op, $rid, $value)';
  Obj interpret(ZincInterpreter interp) {
    if (lid != null) {
      // Not bare.
      op.set(interp, (interp,x,y) {
        interp.push_scope();
        interp.setv(lid.id, x);
        if (rid == null) { assert(y == null); }
        else { interp.setv(rid.id, y); }
        Obj res = value.interpret(interp);
        interp.pop_scope();
        return res;
      });
    } else {
      // Bare.
      if (value is Magicop) {
        op.set(interp, (interp,x,y) => value.interpret_with(interp, x, y));
      } else {
        op.set(interp, (interp,x,y) => (value as Anyop).get(interp)(x, y));
      }
    }
    return null;
  }
}

class Program extends Node {
  final List<OpRewrite> rws;
  final Node expr;
  Program(this.rws, this.expr);
  String toString() => 'Program($rws, $expr)';
  Obj interpret(ZincInterpreter interp) {
    rws.forEach((n) => n.interpret(interp));
    return expr.interpret(interp);
  }
}


// Runtime objects.
typedef Obj OpFuncType(ZincInterpreter interp, Obj x, Obj y);

class Obj {}

class IntObj extends Obj {
  final int value;
  IntObj(this.value);
  String toString() => 'IntObj($value)';
  bool operator==(Obj rhs) => rhs is IntObj && value == rhs.value;
  String dump() => value.toString();
}

class SetObj extends Obj {
  final List<Obj> values;
  SetObj(this.values) {
    if (values.length == 0) { throw new Error('set cannot be empty'); }
  }
  String toString() => 'SetObj($values)';
  bool operator==(Obj rhs) => rhs is SetObj && values == rhs.values;
  String dump() => values.map((x) => x.dump()).reduce((x,y) => x+y);
  List<Obj> vals(ZincInterpreter interp) {
    Obj lenobj = interp.op1['#'](interp, this, null);
    int len;
    if (lenobj is! IntObj) { throw new Error('# operator must return an int'); }
    len = lenobj.value;
    if (len < 0) { throw new Error('result of # operator must be positive'); }
    return new List<Obj>.from(values.getRange(0, len));
  }
}


// Parser.
class ZincParser extends LanguageParsers {
  ZincParser(): super(reservedNames: ['let', 'in', 'join', 'cut']);
  get start => prog().between(spaces, eof);
  get comma => char(',') < spaces;
  get lp => symbol('(');
  get rp => symbol(')');
  get lb => symbol('{');
  get rb => symbol('}');
  get colon => symbol(':');
  get plus => symbol('+');
  get minus => symbol('-');
  get star => symbol('*');
  get slash => symbol('/');
  get eq => symbol('=');
  get len => symbol('#');
  get in_ => char(':');
  get where => char('^');
  get sort => char('\$');

  prog() => reserved['let'] + oprw().sepBy(comma) + reserved['in'] + expr() ^
            (_1,o,_2,x) => new Program(o,x);
  oprw() => oprw1() | oprw2() | oprw3();
  oprw1() => (basicop() | lenop()) + eq + (magicop() | op()) ^
             (o,_,r) => new OpRewrite(o,r);
  oprw2() => (id() + op() + id()).list + eq + expr() ^
             (l,_,x) => new OpRewrite(l[1], x, l[0], l[2]);
  oprw3() => lenop() + id() + eq + expr() ^ (o,a,_,x) => new OpRewrite(o, x, a);
  magicop() => (reserved['join'] | reserved['cut']) ^ (s) => new Magicop(s);
  basicop() => (plus | minus | star | slash | eq) ^ (op) => new Op(op);
  op() => (basicop() + colon ^ (op,_) => new Op(op.op, true)) | basicop();
  lenop() => (len + colon ^ (_1,_2) => new Lenop(true)) |
             len ^ (_) => new Lenop();
  expr() => setcomp() | unop() | binop() | prim();
  setcomp() => lb + id() + in_ + rec(expr) + clause() + rb ^
               (_1,i,_2,x,c,_3) => new SetComp(i,x,c);
  clausekind() => (where ^ (_) => ClauseKind.Where) |
                  (sort  ^ (_) => ClauseKind.Sort);
  clause() => clausekind() + rec(expr) ^ (k,x) => new Clause(k,x);
  unop() => lenop() + rec(expr) ^ (o,x) => new Len(o,x);
  binop() => prim() + op() + rec(expr) ^ (l,o,r) => new Binop(l,o,r);
  prim() => id() | intlit() | parens(rec(expr));
  id() => identifier ^ (i) => new Id(i);
  intlit() => intLiteral ^ (i) => new IntLiteral(i);
}


// Interpreter.
class ZincInterpreter {
  Map<String, OpFuncType> op0, op1;
  List<Map<String, Obj>> scopes;
  ZincInterpreter() {
    var beInt = (v) {
      if (v is IntObj) { return v.value; }
      else { throw new Error('argument to binary operator must be integer'); }
    };
    op0 = {
      '+': (_,x,y) => new IntObj(beInt(x)+beInt(y)),
      '-': (_,x,y) => new IntObj(beInt(x)-beInt(y)),
      '*': (_,x,y) => new IntObj(beInt(x)*beInt(y)),
      '/': (_,x,y) => new IntObj(beInt(x)/beInt(y)),
      '=': (_,x,y) => new IntObj(x == y ? 1 : 0),
      '#': (i,x,_2) =>
        new IntObj(x is IntObj ? x.value.toString().length : x.values.length)
    };
    op1 = new Map<String, OpFuncType>.from(op0);
    scopes = [{}];
  }

  void push_scope() { scopes.add({}); }
  void pop_scope() { scopes.removeLast(); }
  void setv(String name, Obj value) { scopes[scopes.length-1][name] = value; }
  Obj getv(String name) {
    for (var scope in scopes.reversed) {
      if (scope[name] != null) { return scope[name]; }
    }
    if (name == 'S') {
      var input = stdin.readLineSync();
      var list = new List.from(input.codeUnits.map((c) =>
        new IntObj(int.parse(new String.fromCharCodes([c])))));
      setv('S', new SetObj(list));
      return getv('S');
    } else throw new Error('undefined variable $name');
  }
}


void main(List<String> args) {
  if (args.length != 1) {
    print('usage: ${Platform.script.toFilePath()} <file to run>');
    return;
  }
  var file = new File(args[0]);
  if (!file.existsSync()) {
    print('cannot open ${args[0]}');
    return;
  }
  Program root = new ZincParser().start.parse(file.readAsStringSync());
  ZincInterpreter interp = new ZincInterpreter();
  var res = root.interpret(interp);
  print(res.dump());
}
