# A084030 - "only one term is zero" on the diagonal of A084029, formalized in Lean 4

Machine-checked resolution of the conjecture recorded in the
comments of [OEIS A084030](https://oeis.org/A084030)
(Amarnath Murthy, 2003): the main diagonal of the triangle
A084029 has **only one zero term** - `a(2) = 0`, all other
terms nonzero. Corollary of the already machine-checked
[OEIS A084029](https://oeis.org/A084029) row-existence
theorem (sibling package).

## Theorems

The diagonal term itself is a formalized object: `a084030_val n`
is the n-th smallest witness of row `n` of A084029 (the `sInf`
of the set of witnesses preceded by at least `n-1` smaller
witnesses; `0` when the row has fewer than `n` terms, matching
the OEIS padding convention).

```lean
theorem A084030Val.a084030_val_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    a084030_val n = 0 ↔ n = 2
theorem A084030 (n : ℕ) (hn : 3 ≤ n) : n ≤ (witnesses n).card
theorem A084030_zero_unique : (witnesses 2).card = 1 -- a(2) = 0
theorem A084030_one : (witnesses 1).card = 1 -- a(1) = 1
theorem A084030Val.a084030_val_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < a084030_val n
```

Value anchors, kernel-certified against the entry data:
`a(1) = 1`, `a(2) = 0`, `a(3) = 120`, `a(4) = 2020`,
`a(5) = 10400`, `a(6) = 100140`, `a(7) = 1001203`,
`a(8) = 10001312`, `a(9) = 100000080`, `a(10) = 1000000900`,
`a(11) = 10000010108`, `a(12) = 100000000524`,
`a(13) = 1000000002235`, `a(14) = 10000000002650`,
`a(15) = 100000000000950`, `a(16) = 1000000000003408`
(theorems `a084030_val_one`, `a084030_val_two`,
`a084030_val_3` .. `a084030_val_16`; each anchor certifies
the complete list of smaller witnesses by kernel `decide`
over the multiples of `n` in `[10^(n-1), a(n))`).

Companion corollary (quotient triangle A084033, no conjecture
on that entry):

```lean
theorem A084033 (n : ℕ) (hn : 3 ≤ n) :
    n ≤ ((witnesses n).image (· / n)).card ∧
      ∀ q ∈ (witnesses n).image (· / n), 0 < q
```

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake build` - exit 0, **zero `sorry`**, zero `admit`
- `#print axioms` on every exported theorem:
  `[propext, Classical.choice, Quot.sound]` - the three
  standard axioms only. **No `native_decide`, no
  `ofReduceBool`, no `sorryAx`.** The trusted base is the
  Lean kernel alone: the A084029 witness table
  `table029_ok_all` (rows `n ≤ 130`) is certified by
  split `decide +kernel` certificates (modules
  `Scratch029_cert_*`, one `interval_cases` + `decide
  +kernel` per sub-range).

## Proof idea

`witnesses n` is the *complete* row-`n` set (every `n`-digit
`N` satisfies `N < 10^n`). The A084029 theorem supplies a
Finset of `≥ n` witnesses for `n ≥ 3`, included in
`witnesses n`; the maximum of any `n`-element subset then
has `≥ n-1` smaller witnesses, so `Tdiag n` is nonempty and
`a084030_val n` is a genuine `n`-digit witness, hence nonzero.
For `n = 2` the witness set is the singleton `{20}` (kernel
`decide`), `Tdiag 2` is empty and `a(2) = 0`; for `n = 1`,
`a(1) = 1`. Uniqueness of the zero follows.

## Contents

- `A084030.lean` - the row-cardinality corollary (`witnesses`,
  `mem_witnesses`, `card_witnesses_ge`, theorems `A084030`,
  `A084030_zero_unique`, `A084030_one`)
- `A084030Val.lean` - the diagonal object: `Tdiag`,
  `a084030_val`, position certificate `a084030_val_eq`,
  non-emptiness `tdiag_nonempty`, `a084030_val_pos`, the
  zero-characterization `a084030_val_zero_iff` and the
  kernel-certified anchors `a084030_val_one`,
  `a084030_val_two`, `a084030_val_3` .. `a084030_val_16`
- `A084033.lean` - companion corollary (quotient rows)
- `A084029.lean` - the row-existence theorem (two-block
  construction for `n ≥ 131`, certified table below)
- `A084029Table.lean` - the 128-row witness table (data)
- `Scratch029_cert_{lo,hi1,hi2a,hi2b,hi2c,hi2d}.lean` -
  the split kernel `decide +kernel` certificates of the
  table, assembled in `table029_ok_all`
- `A077754.lean`, `A077754Cert.lean`, `CornerTable.lean` -
  dependency chain (digit-fibre engine, kernel `decide`
  certificates)
- `lakefile.toml`, `lean-toolchain` (v4.35.0),
  `lake-manifest.json` (pins mathlib v4.35.0)

## Reproduce

```sh
cd lean-artifact
lake exe cache get # fetches mathlib v4.35.0 oleans
lake build         # builds the whole chain, exit 0
```

## Reference

Companion paper `A084030-paper.tex` in the project package;
sibling: *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*, F. Gaudin -
https://doi.org/10.5281/zenodo.23879088
