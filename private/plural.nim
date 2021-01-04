import parseutils

# inspired from : http://www.coderslexicon.com/convert-infix-to-postfix-in-c/

type
    Operator* = enum
        INVALID, ADD, SUB, MOD, DIV, MUL, LE, EQ, LT, GT, GE, NE, AND, OR, TERNARY, PARENT_OPEN, PARENT_CLOSE, CONSTANT, VARIABLE

    State* = object
        case kind: Operator
        of CONSTANT:
            value: int
        else:
            nil

let precedance = [ 0, # INVALID
                  60, 60, 50, 50, 50,     # ADD, SUB, MOD, DIV, MUL
                  80, 80, 80, 80, 80, 80, # LT, EQ, LT, GT, GE, NE
                  130, 140, 150,          # AND, OR, TERNARY
                  0, 0, 0, 0]             # PARENT_OPEN, PARENT_CLOSE, CONSTANT, VARIABLE
                  #

proc lookup(ch: char, next: char; pos: var int): Operator =
    case ch:
    of '+': result = ADD
    of '-': result = SUB
    of '*': result = MUL
    of '/': result = DIV
    of '%': result = MOD
    of '<':
        if next == '=': result = LE; pos += 1
        else:           result = LT
    of '>':
        if next == '=': result = GE; pos += 1
        else:           result = GT
    of '=':
        if next == '=': result = EQ; pos += 1
        else:           result = INVALID
    of '!':
        if next == '=': result = NE; pos += 1
        else:           result = INVALID
    of '|':
        if next == '|': result = OR; pos += 1
        else:           result = INVALID
    of '&':
        if next == '&': result = AND; pos += 1
        else:           result = INVALID
    else:   result = INVALID

proc compare(a, b: Operator): int =
    let A = precedance[a.ord]
    let B = precedance[b.ord]
    result = cmp(A, B)

proc `$`*(x: State): string =
    result =""
    case x.kind
    of VARIABLE:
        result = "N"
    of CONSTANT:
        result = $x.value
    else:
        result = $x.kind

proc evaluate*(symbols: openArray[State]; value: int): int =
    ## This calculator evaluates postfix expressions using a stack. The following rules are used:
    ## If the next symbol is an operand (a number), put it on top of the stack.
    ## If the next symbol is an operator, remove the top two numbers from the stack, perform the operation, and place the result on top of the stack. *
    var stack = newSeq[int]()

    for s in symbols:
        case s.kind
        of CONSTANT:
            stack.add s.value
        of VARIABLE:
            stack.add value
        of ADD, SUB, MOD, DIV, MUL, LE, EQ, LT, GT, GE, NE, AND, OR:
            let B = stack.pop
            let A = stack.pop
            case s.kind
            of ADD: stack.add A + B
            of SUB: stack.add A - B
            of MOD: stack.add A mod B
            of DIV: stack.add A div B
            of MUL: stack.add A * B
            of LE: stack.add( (A <= B).int)
            of EQ: stack.add( (A == B).int)
            of LT: stack.add( (A < B).int)
            of GT: stack.add( (A > B).int)
            of GE: stack.add( (A >= B).int)
            of NE: stack.add( (A != B).int)
            of AND: stack.add( (A and B).int)
            of OR: stack.add( (A or B).int)
            else: echo("error: ", s.kind)
        of TERNARY:
            let C = stack.pop
            let B = stack.pop
            let A = stack.pop
            stack.add( if A != 0: B else: C)
        else:
            echo "ignore: ", s.kind

    result = stack.pop

proc parse_constant(buf: string, pos: var int): int =
    while pos < len(buf) and buf[pos] in {'0'..'9'} :
        result = (result * 10) + (ord(buf[pos]) - ord('0'))
        inc(pos)

proc parseExpr*(str: string) : seq[State] =
    var pos = skipWhitespace(str, 0)
    result = newSeq[State]()
    var operators = newSeq[State]()
    while pos < str.len:
        let ch = str[pos]
        case ch
        of '0'..'9': result.add State(kind:CONSTANT, value:parse_constant(str, pos)); pos -= 1
        of 'n', 'N': result.add State(kind:VARIABLE)
        of '(': # new group
            operators.add State(kind:PARENT_OPEN)

        of ')': # end group
            while operators.len != 0:
                if operators[^1].kind == PARENT_OPEN:
                    discard operators.pop()
                    break
                result.add operators.pop()

        of '+', '-', '*', '/', '%', '<', '>', '=', '!','|', '&': # Binary operators
            let kind = lookup(ch, str[pos + 1], pos)
            while operators.len != 0 and operators[^1].kind != PARENT_OPEN and
                  compare(operators[^1].kind, kind) <= 0:
                result.add operators.pop()
            operators.add(State(kind:kind))

        of ':', '?': # Ternary operators
            while operators.len != 0 and operators[^1].kind != PARENT_OPEN: # ternary is lowest precedence
                result.add operators.pop()
            if ch == ':': # closing ternary
                operators.add(State(kind:TERNARY))
            operators.add(State(kind:PARENT_OPEN))

        else: # closing ternary
            echo("ignored: ", ch)

        pos += 1
        pos += skipWhitespace(str, pos)

    while operators.len != 0:
        let op = operators.pop()
        if op.kind != PARENT_OPEN:
            result.add op
