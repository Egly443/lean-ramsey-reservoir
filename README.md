# Reservoir and book calculus for greedy Ramsey arguments

[![CI](https://github.com/Egly443/lean-ramsey-reservoir/actions/workflows/ci.yml/badge.svg)](https://github.com/Egly443/lean-ramsey-reservoir/actions/workflows/ci.yml)

A Lean 4 library of the state machine behind greedy clique-building arguments in Ramsey theory:
reservoirs (a clique plus a pool of common neighbours) and two-colour reservoirs with a Pascal
potential, Ramsey bounds, books, and homogeneous block quotients. The Erdős–Szekeres bound,
`R(3, 3) = 6`, the codegree–triangle identity, book bounds from triangle and edge density, and
book forcing all follow from the same few lemmas.

It is a **Mathlib-ready strawman**, written to Mathlib's conventions and offered for reuse as is,
by people and by AI systems. Anyone in the Mathlib community may upstream it, in whole or in part,
if and when they choose. The author does not plan to drive it through Mathlib review.

**Provenance:** AI-generated with human guidance. Every file:

* builds with no `sorry` and no warnings;
* uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
* passes Mathlib's `#lint`, `runLinter` and `lint-style`, and the `linter.mathlibStandardSet`
  linters;
* depends only on Mathlib;
* meets [LeanPool](https://github.com/LeanPool/lean-pool)'s content rules (file headers, no
  waivers or `set_option`).

Licensed under Apache 2.0.

Edge two-colourings of a complete graph are written as a graph `G` (red) and its complement `Gᶜ`
(blue), so every statement is about Mathlib's `SimpleGraph`, `IsNClique` and `CliqueFree`.

## Using it

The library is pinned to Lean and Mathlib `v4.35.0-rc3` (see `lean-toolchain` and
`lakefile.toml`). To depend on it, add to your `lakefile.toml`:

```toml
[[require]]
name = "ramsey_reservoir"
git = "https://github.com/Egly443/lean-ramsey-reservoir"
rev = "main"
```

and `import RamseyReservoir`, or import individual modules. To build it, run `lake exe cache get`
and then `lake build`.

Releases are tagged `vX.Y.Z` from `main` by the manually triggered `Release` workflow
(`.github/workflows/release.yml`).

## Contents

| File | Main results |
|---|---|
| `RamseyReservoir/Reservoir.lean` | `SimpleGraph.Reservoir G`: a clique `spine` and a disjoint `pool` of common neighbours. `pivot` moves a pool vertex onto the spine and keeps its neighbours; `card_pivot_pool` gives the exact loss; `isNClique_union` glues a pool clique to the spine; `Step` and `Reaches` (runs of pivots) with monotonicity. **Greedy clique** `Reservoir.exists_isNClique_of_card_nonadj_le`: if every pool vertex has at most `d` non-neighbours in the pool and `j * d < #pool`, there is a `(#spine + j + 1)`-clique. Corollary `exists_isNClique_of_minDegree`: minimum degree `δ` with `j * (n - δ) < n` forces a `(j + 1)`-clique (so `δ > (1 - 1/k) n` forces `K_{k+1}`). Also `IsClique.union_of_forall_adj`. |
| `RamseyReservoir/RamseyBound.lean` | `SimpleGraph.RamseyBound n r s`: every graph on `Fin n` has an `r`-clique or an independent `s`-set (so `R(r, s)` is the least such `n`). Transfer to any finite vertex set of size `≥ n` in any graph (`RamseyBound.exists_isNClique_subset`, `RamseyBound.not_cliqueFree_or`), monotonicity, symmetry, the trivial bounds, and positivity. |
| `RamseyReservoir/Bireservoir.lean` | `SimpleGraph.Bireservoir G`: a red clique, a blue clique and a common pool, with `redPivot` and `bluePivot`; the two retained pools partition the pool minus the pivot (`card_redPivot_pool_add_card_bluePivot_pool`). **Potential:** a state is `IsWinning R r s` when `R (r - #red) (s - #blue) ≤ #pool`; for `R` satisfying Pascal's inequality (`IsPascal`), `IsWinning.exists_pivot` keeps the state winning and `IsWinning.exists_isNClique` reaches a red `K_r` or a blue `K_s`. Consequences: `ramseyBound_of_pascal` (every Pascal threshold is a Ramsey bound); `isPascal_choose` (the binomial threshold is Pascal), hence **Erdős–Szekeres** `ramseyBound_choose` (`R(r + 1, s + 1) ≤ C(r + s, r)`); the Erdős–Szekeres recursion `RamseyBound.add`, proved directly by one pivot; `ramseyBound_four_pow`, and `R(3, 3) = 6` (`ramseyBound_six_three_three`, `not_ramseyBound_five_three_three` via the five-cycle). `exists_of_ramseyBound`: a pool large enough for the missing clique sizes wins. |
| `RamseyReservoir/Book.lean` | `SimpleGraph.ContainsBook G m t`: an `m`-clique with `t` common neighbours, i.e. a reservoir with an `m`-vertex spine. `containsBook_two_iff` (an edge with `t` common neighbours). **Codegrees count triangles:** `sum_card_commonNeighbors_eq` (`∑` over ordered adjacent pairs of the codegree is `6 · #triangles`, via `card_orderedTriangles`). Books from triangle density (`containsBook_two_of_mul_card_edgeFinset_le`, `t · e ≤ 3T`) and from edge density (`exists_adj_four_mul_card_edgeFinset_le`, an edge with `4e ≤ n (codeg + n)`), with the book form of Mantel's theorem (`exists_adj_card_commonNeighbors_pos`). **Book forcing:** `Reservoir.exists_of_ramseyBound`, `ContainsBook.not_cliqueFree_or`, `not_cliqueFree_or_of_mul_card_edgeFinset_le`. Also `degree_add_degree_le_card_commonNeighbors_add`. |
| `RamseyReservoir/HomogeneousBlocks.lean` | `SimpleGraph.HomogeneousBlocks G ι`: disjoint nonempty blocks, all-or-nothing between blocks, with `quotient` graph on `ι` and representatives `rep`. Quotient cliques and independent sets lift (`isNClique_map_rep`, `isNClique_compl_map_rep`); **anchored gluing** `isNClique_anchor` (an `n`-clique in one block of an `m`-clique of the quotient gives an `(n + m - 1)`-clique); `exists_of_ramseyBound` on the quotient. |

`Reservoir` is the one-colour state; `Bireservoir` pairs a reservoir of `G` with one of `Gᶜ` on the
same pool. There are two kinds of win. A win from a *supplied* Ramsey bound (`exists_of_ramseyBound`,
`RamseyBound.add`, book forcing) applies `RamseyBound.exists_isNClique_subset` to the pool and
glues the result to a spine with `Reservoir.isNClique_union`. The Pascal potential
(`IsWinning.exists_isNClique`) needs no supplied bound: it pivots until one spine reaches its
target and then trims that spine. Books are reservoirs with a fixed spine size, so book forcing is
the first kind of win.

## Notes for anyone upstreaming to Mathlib

* **Placement.** `RamseyBound.lean` would start a `Mathlib/Combinatorics/SimpleGraph/Ramsey/`
  directory, with `Reservoir.lean`, `Bireservoir.lean` and `HomogeneousBlocks.lean` next to it.
  `Book.lean` would go to `Mathlib/Combinatorics/SimpleGraph/Book.lean`; its codegree–triangle
  identity could join `Mathlib/Combinatorics/SimpleGraph/Triangle/Counting.lean`.
* **Lemmas that belong elsewhere.** `IsClique.union_of_forall_adj` and
  `IsClique.exists_isNClique_subset` belong in `Mathlib/Combinatorics/SimpleGraph/Clique.lean`;
  `exists_isNClique_of_minDegree` next to `Extremal/Turan.lean`;
  `degree_add_degree_le_card_commonNeighbors_add` in `Finite.lean`, next to the other
  `card_commonNeighbors` lemmas.
* **Names.** `ContainsBook` rather than `HasBook`, to leave the shorter name free for the
  common special case `m = 2` (an edge with `t` common neighbours). `RamseyBound` rather than a Ramsey number: Mathlib has no
  Ramsey number, and bounds compose without committing to a definition of `R(r, s)`.
* **Overlap with Mathlib.** None. Mathlib's Turán theorem (`CliqueFree.card_edgeFinset_le`) gives
  Mantel's theorem by a different route; here Mantel falls out of the book bound.
* **Design questions.** `RamseyBound` is stated on `Fin n`, which avoids universe parameters, and
  transferred to arbitrary finite sets by an embedding. Two-colourings are `G` and `Gᶜ` rather than
  an edge labelling, as Mathlib does for independent sets (`Gᶜ.IsClique s ↔ G.IsIndepSet s`).
  Codegrees are Mathlib's `Fintype.card (G.commonNeighbors u v)`; sums over ordered adjacent pairs
  avoid `Sym2`.
* **Older Mathlib.** The quotient graph is built with `SimpleGraph.fromRel`, whose interface is the
  same on both versions (the `symm` field of `SimpleGraph.mk` changed type between them).

## Relation to other libraries

[LeanPool](https://github.com/LeanPool/lean-pool) has no Ramsey-bound, book or reservoir project (its Ramsey-related projects are
Nash-Williams' infinite theory, multicolour triangle Ramsey numbers and Erdős–Tuza–Valtr). TauCeti has none. [lean-ramsey](https://github.com/Egly443/lean-ramsey)
defines Ramsey numbers through `Arrow` and proves the binomial bound by a direct recursion; this
package reaches the same bound as the binomial instance (`isPascal_choose`) of a general potential
argument (`ramseyBound_of_pascal`), with a
`RamseyBound` predicate that does not depend on lean-ramsey's definitions.

Bhavik Mehta's formalisation of the Campos–Griffiths–Morris–Sahasrabudhe exponential improvement
for diagonal Ramsey numbers (`b-mehta/exponential-ramsey`, Lean 3, announced on the Lean Zulip,
*maths*, "A recent proof about Ramsey numbers", November 2023) is built around a book
algorithm; it is not in Mathlib, and neither are Mehta's small Ramsey numbers (Zulip, *Is there
code for X?*, "Small Ramsey numbers", 2024). Lawrence Paulson's Isabelle formalisation of the same
paper is in the Archive of Formal Proofs. This package is written independently of both and is
not derived from either; it supplies the elementary reservoir and book bookkeeping that such
arguments use.

## Not included

* Monochromatic books in two-colourings (book Ramsey numbers): the averaging needs Goodman's
  counting of monochromatic triangles, which belongs in a separate library.
* The book algorithm of Campos, Griffiths, Morris and Sahasrabudhe itself (its density-boost and
  big-blue steps and their analysis): out of scope; this library supplies only the state machine
  it runs on.
* Sharper book bounds just above the Mantel threshold `e = n²/4`: the averaging bounds here give
  `4e/n - n` pages, and sharper results need separate arguments.
* A Ramsey-number function `R(r, s)`: left to lean-ramsey and to any future Mathlib definition;
  everything here is phrased with `RamseyBound`.

## Citation

The mathematics is from the works below. BibTeX entries for Mathlib's `docs/references.bib` are in
`references.bib`. Each was checked against zbMATH or the Jahrbuch (JFM), carries its identifier,
and the file is normalised with the `bibtool` command from Mathlib's `scripts/lint-bib.sh`.

* P. Erdős, G. Szekeres, *A combinatorial problem in geometry*, Compos. Math. 2 (1935), 463–470.
* M. Campos, S. Griffiths, R. Morris, J. Sahasrabudhe, *An exponential improvement for diagonal
  Ramsey*, Ann. of Math. (2) 203 (2026), 869–932, doi:10.4007/annals.2026.203.3.4.
* W. Mantel, *Vraagstuk XXVIII*, Wiskundige Opgaven 10 (1907), 60–61.
