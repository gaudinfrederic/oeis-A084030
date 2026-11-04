# A084030 — "only one term is zero" on the diagonal of A084029, formalized in Lean 4

Machine-checked resolution of the conjecture recorded in the
comments of [OEIS A084030](https://oeis.org/A084030)
(Amarnath Murthy, 2003): the main diagonal of the triangle
A084029 has **only one zero term** — `a(2) = 0`, all other
terms nonzero. Corollary of the already machine-checked
[OEIS A084029](https://oeis.org/A084029) row-existence
theorem (sibling package).

## Theorem

For every `n ≥ 3` the witness set
`W(n) = {N < 10^n : n ∣ N, digits(N) has length n, sum n}` has
at least `n` elements — row `n` is full, no zero-padding, so
the diagonal term `a(n)` is a genuine `n`-digit number.

```lean
theorem A084030 (n : ℕ) (hn : 3 ≤ n) : n ≤ (witnesses n).card
theorem A084030_zero_unique : (witnesses 2).card = 1   -- a(2) = 0
theorem A084030_one : (witnesses 1).card = 1           -- a(1) = 1
```

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake env lean A084030.lean` — exit 0, **zero `sorry`**
- `#print axioms` — `A084030_zero_unique` and `A084030_one`
  are kernel-pure (`decide` on ranges 100 and 10):
  `[propext, Classical.choice, Quot.sound]`. `A084030` and
  `A084033` carry the three standard axioms **plus one
  disclosed `native_decide` certificate** — the A084029
  witness table `table029_ok_all` (128 rows of witnesses up
  to 130 digits, too large for kernel evaluation under a 4 GB
  cap; see VERIFICATIONS/axioms.txt). **No `sorryAx`.**

## Proof idea

`witnesses n` is the *complete* row-`n` set (every `n`-digit
`N` satisfies `N < 10^n`). The A084029 theorem supplies a
Finset of `≥ n` witnesses for `n ≥ 3`, included in
`witnesses n`; `Finset.card_le_card` concludes. For `n = 2`
the set is the singleton `{20}` (kernel `decide`), hence row
`[20, 0]` and the unique zero.

## Contents

- `A084030.lean` — the corollary file (`witnesses`,
  `mem_witnesses`, `card_witnesses_ge`, the three theorems)
- `A084033.lean` — companion corollary: for `n ≥ 3` the
  quotient row `T(n,k) = A084029(n,k)/n` has `≥ n` integer
  terms, all nonzero (no conjecture on that entry)
- `A084029.lean`, `A077754.lean`, `A077754Cert.lean`,
  `CornerTable.lean` — dependency chain (existence theorem +
  digit-fibre engine)

## Reproduce

```sh
# elan installs leanprover/lean4:v4.35.0 via lean-toolchain
lake exe cache get                    # fetches mathlib v4.35.0 oleans
lake build                            # builds the whole chain
lake env lean -M 4096 -j 2 A084030.lean   # -> exit 0 + axiom audits
lake env lean -M 4096 -j 2 A084033.lean
```

## Reference

Companion paper `A084030-paper.tex` in the project package;
sibling: *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*, F. Gaudin —
https://doi.org/10.5281/zenodo.23879088
