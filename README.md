# Simple Fact Engine

A simple program for collecting facts, which constitute a statement with an optional list of arguments in parentheses, and then querying the collected facts to produce answers. For example:

```
$ cargo run
> INPUT has_friends(bocchi)
> INPUT has_friends(nako)
> QUERY has_friends(aru)
---
false
> QUERY has_friends(bocchi)
---
true
> INPUT are_friends(bocchi, nako)
> INPUT are_friends(mayo, sotoka)
> QUERY are_friends(bocchi, nako)
---
true
> QUERY are_friends(bocchi, X)
---
X: nako
> QUERY are_friends(X, Y)
---
X: bocchi, Y: nako
X: mayo, Y: sotoka
> INPUT are_friends(aru, aru)
> QUERY are_friends(X, X)
---
X: aru
> EXIT
```

Variables in queries, such as `X` and `Y` above, start with an uppercase letter, while other values are treated as _symbols_, which also includes numbers since the engine gives no special consideration to numeric values.

The first word on each line is the command, either `INPUT`, `QUERY`, or `EXIT`.

## Prior Art

The fact engine and its pattern matching is similar to the basis of a typical logic programming language, such as [Prolog](https://www.swi-prolog.org). [Erlang](https://www.erlang.org) uses a similar approach when matching function invocations to function clauses.
