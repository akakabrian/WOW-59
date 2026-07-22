# WOW II Conjecture 59 — Status

## STATUS

**FALSE — explicit 18-vertex counterexample found.**

Current isolated verification target:

- repository: `akakabrian/WOW-59`
- branch: `agent/kernel-check`
- draft PR: `#1`
- current head: `2fa37b62916dccb2e986281b7f754d5000436649`
- current Actions run: `29887784148`

Nothing has been merged or submitted upstream.

## PROVEN

The graph certificate establishes mathematically:

- `residue G = 10`;
- `17 ≤ b G`;
- `largestInducedForestSize G ≤ 13`;
- `G.Connected`.

Therefore `169 < residue(G) * b(G)`, hence `13 < sqrt(residue(G) * b(G))`, contradicting the conjectured ceiling inequality.

Independent exact Python and C evaluators returned `(residue,b,f) = (10,17,13)`.

The Lean source now uses only kernel-reduced finite certificates. The two structural searches range over `Finset (Fin 10)` rather than `Finset (Fin 18)`:

- every selected core set of size at least six contains an edge;
- every selected core set of size at least seven contains a 4-cycle.

The remaining seven leaves and universal center are handled by symbolic cardinality arguments. No native decision tactic is used.

CI is configured to fail on:

- any Lean build or warning-as-error failure;
- `sorry`, `admit`, custom `axiom`, `unsafe`, or native decision tactics in the certificate;
- `Lean.ofReduceBool`, `Lean.trustCompiler`, or `sorryAx` in the axiom audit.

## OPEN

Lean elaboration, kernel checking, and final axiom-output review remain open. GitHub Actions run `29887784148` is queued and has not yet received a hosted runner; it has not reported a compiler failure.

## NEXT

When the queued run executes, inspect `lean-ci.log`, patch only concrete Lean diagnostics if necessary, and repeat until green. After a successful build and clean axiom report, close the draft PR without merging. No upstream submission without separate approval.
