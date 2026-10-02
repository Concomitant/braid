# Writing

Prose rules for this project. They cover `README.md`, `MANUAL.md`,
`CONSTRUCTS.md`, `GLOSSARY.md`, and the comments in `examples/*.braid`.
They do not cover `design-*.md` or `READING.md`: those are dated
histories, amended and never rewritten.

## Say the thing

One idea per sentence. Lead with the claim; the reason follows. No
sentence exists to announce the next sentence.

Define a term once, in **bold**, where it first appears, then use it
without ceremony. One spelling per thing: do not alternate `carrier`
and `hom-object`, or "slot" and "generator", for the same concept in
one section. `GLOSSARY.md` holds the terms and settles ties.

Use a table for three or more parallel items. Use a code block for
anything you would otherwise put in backticks twice in one sentence.
Write "refused", "accepted", "reports", "requires", "mints" for what
the checker does.

## Banned

An em-dash as a connective. Use a period, a comma, or restructure the
sentence. One em-dash per paragraph is allowed for a true parenthetical.
A reference table may keep ` — ` as a fixed separator between a type
and its gloss; that is a column, not a sentence.

| banned | write instead |
|---|---|
| "it is worth noting", "notably", "crucially", "importantly", "interestingly" | the claim, with nothing in front of it |
| "the key insight is", "the point is", "the whole point" | the claim |
| "genuinely", "honestly", "honest" on a technical claim | nothing |
| "sharp", "clean", "load-bearing", "principled" as praise | what the design does |
| "exactly", "precisely" as emphasis | nothing; keep them as measurement, as in "exactly one wire" |
| "not X, but Y" and "X, not Y" as a frame | "Y" |
| a sentence ending "and that is the point" or "which is the point" | end on the claim |
| "here is the thing", "let me be clear", "to be clear" | nothing |
| "So," and "Now," as sentence openers | nothing |
| "may possibly", "it seems that perhaps" | one hedge, or none |
| the checker "knows", "wants", "sees", "notices", "is happy" | "checks", "requires", "reports", "refuses", "accepts" |

Also out: rhetorical triplets built for rhythm, bold on the first words
of every bullet in a list, and a closing paragraph that restates the
section. Do not end a section with an offer or a promise.

## Agent-report phrasing

A reference describes the language as it is. These belong to the work
that produced it, not to the reference: "delivered as scoped", "pinned",
"shipped", "byte-identical", "verified in Docker", "the agent", "the
lead", stage numbers such as `5c½` or `7b`, commit hashes, and dates.

One exception. A section may carry a single dated line at its top
saying when the behaviour it describes last changed:

```
*Last changed 2026-09-18.*
```

Everything below that line describes the current state. A section
written as a stack of amendments stacked on each other gets consolidated
into one description with one such line. Reference text never says what
something used to be; that is what `design-*.md` is for.

## Do not change meaning

Editing prose is not editing the language. If you cannot tell what a
sentence claims, run the example or the REPL and find out. If the
sentence is wrong, fix it and say so. MANUAL's types are checked against
the implementation by the test suite, so a wrong edit to a type in prose
fails a test. Every example's printed output stays byte-identical across
a prose pass; if it moves, you edited code.
