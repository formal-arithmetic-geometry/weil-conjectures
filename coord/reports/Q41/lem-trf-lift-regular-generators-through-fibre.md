## Worker report

The module `Sheaf.RingTheory.LiftRegularGeneratorsThroughFibre` states
`Ideal.lift_regular_generators_through_fibre`, with its whole proof `by sorry`.
It adds no definitions. The node's mathematical statement and dependency lists are unchanged.
Source read: Stacks More on Algebra, Tag 066A, `lemma-independence-of-generators`,
part (1); Algebra, Tags 00LN, `lemma-regular-quasi-regular`, and 061S,
`lemma-quasi-regular-regular`. Also read the cited final paragraph of
`lemma-ci-well-defined` and the recorded local Nakayama interface.

Hypothesis-by-hypothesis correspondence:

- `R : Type u`, `S : Type v`, `[CommRing R]`, `[CommRing S]` give the two commutative
  unital rings, with independent universes. `[IsLocalRing R]` and `[IsLocalRing S]`
  give the local rings and already include `Nontrivial`, as Mathlib's class extends it.
  `[IsNoetherianRing R]` and `[IsNoetherianRing S]` give their Noetherianity.
- `c : R →+* S` with `[IsLocalHom c]` is the local homomorphism. Mathlib's
  `IsLocalRing.local_hom_TFAE` identifies this with mapping the source maximal ideal
  into the target maximal ideal; no flatness or surjectivity of `c` is assumed.
- `σ : (R ⧸ maximalIdeal R) ≃+* (S ⧸ maximalIdeal S)` and `hσ` specify the induced
  residue-field isomorphism: on the class of every `a : R`, its value is the class
  of `c a`. Thus `σ` is the given canonical induced map, not an unrelated field
  isomorphism. The quotients are literally the rings underlying `IsLocalRing.ResidueField`.
- `I : Ideal R`, `hI : I ≤ maximalIdeal R` and `hIfg : I.FG` render the ideal,
  its containment in the maximal ideal and its finite generation. `J` is everywhere
  the actual extended ideal `I.map c`, so no extra ideal or comparison is assumed.
- The source generator space is `I ⧸ (maximalIdeal R • (⊤ : Submodule R I))`.
  This scalar multiple is the product ideal `m I` viewed inside `I`, not inside `R`.
  The target uses the same construction over `S` on `I.map c`, giving `J/nJ`.
  Their scalar actions over `R/m` and `S/n` are Mathlib's quotient module actions.
- `β` is a semilinear map for `σ.toRingHom`, and `hβbij : Function.Bijective β`
  says it is an isomorphism. Semilinearity through `σ` is precisely linearity over
  the common residue field in the node. `hβ` specifies its value on EVERY quotient
  representative `a : I`, namely the class of `c a` in `J/nJ`. The subtype membership
  is supplied by the existing `Ideal.mem_map_of_mem`. Since every quotient class
  has a representative, this characterization uniquely determines the canonical map.
  Thus no arbitrary comparison map replaces the induced generator-space map.
- `r : ℕ`, `y : Fin r → I.map c` are the ordered tuple in `J`. `hy` puts every entry
  in `n`, `hyreg` states regularity using Mathlib's `RingTheory.Sequence.IsRegular S`
  on `List.ofFn` of the underlying elements, and `hygen` states that their ideal
  span is `I.map c`. Choosing subtypes for membership in `J` adds no restriction:
  any tuple generating `J` has these unique subtype lifts.

Conclusion-by-conclusion correspondence:

- The first conjunct gives a basis `b` of `I/mI` with `β (b i) = [y i]` for all
  indices. This says exactly that `[y i]` is a basis of `J/nJ` over `k`: a bijective
  semilinear map for the residue-field isomorphism transports bases, in both
  directions. This formulation uses the source field `k = R/m` directly and avoids
  introducing a second scalar action on the target quotient. It also preserves the
  specified ORDER of the tuple and all its entries.
- The second conjunct quantifies over EVERY `Module.Basis (Fin r) (R/m) (I/mI)`
  and EVERY `f : Fin r → I` satisfying `[f i] = b i`. Its first conclusion is
  `Ideal.span (Set.range (fun i ↦ (f i).val)) = I`, exactly generation of `I`.
  Its second is regularity of `List.ofFn (fun i ↦ c (f i))` over `S`.
  Its third is generation of `J = I.map c` by that same image tuple.
  The lifts are not required to map to the original entries `y i`.
- The third conjunct asserts existence of a length-`r` basis of `I/mI` and lifts of
  all its entries. Together with the universal second conjunct, these are exactly
  the bases and lifts asserted to exist in the node, with generation and regularity.

Recorded statement dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: every ideal is finite.
- `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`:
  each successive multiplication is injective and the final quotient is nonzero.

Other existing interfaces used are `Module.Basis` from
`Mathlib.LinearAlgebra.Basis.Defs`, ideal extension and quotient modules, and
`IsLocalHom` and maximal ideals from the public local-ring imports.
The proof imports include every currently recorded project proof dependency:
`Sheaf.RingTheory.LocalGeneratingTuples` (`Module.exists_elementary_generating_tuple_change`),
`Sheaf.RingTheory.RegularSequenceGradedPolynomial` (`Ideal.regularSequence_gradedPolynomial`),
and `Sheaf.RingTheory.QuasiRegularNoetherianLocal`
(`RingTheory.Sequence.quasiRegularNoetherianLocal`). The recorded Nakayama Mathlib match
`IsLocalRing.map_mkQ_eq_top` is supplied by `Mathlib.RingTheory.LocalRing.Module`.
`lem-trf-regular-ideal-residue-basis-prescribed-generator` has no Lean record or Mathlib
match in the read clone and is a proof-only dependency, so has no module to import.
The docstring records all six proof steps and their DAG references.

Edge cases checked before drafting:

- At `r = 0`, `Fin 0` and its `List.ofFn` give the empty tuple. `hygen` forces
  `J = 0`; the assumed `β` makes `I/mI` zero, and Nakayama gives `I = 0`.
  Empty bases and lifts are allowed, and the empty sequence is regular over the
  nonzero ring `S`. There is no `0 < r` restriction.
- If `I = 0`, then `J = 0`. A positive-length regular generating tuple of zero
  cannot occur in a nonzero ring, while the empty case is included.
- Zero rings are excluded exactly by the node and Mathlib's local-ring classes.
  Fields, arbitrary characteristics, noninjective local maps, and independent ring
  universes remain permitted. No regularity of `R` or `S` is imposed.
- Arbitrary bases, arbitrary representatives and arbitrary ordering are all retained.

Searches (2026-10-24), using the prescribed `msearch.py` wrapper:

- LeanFinder: `A local homomorphism inducing an isomorphism on ideal generator spaces
  lifts any basis to generators whose images form a regular sequence`. Eight hits,
  including `IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem`, its localization
  variant, and `Module.exists_basis_of_basis_baseChange`. These concern localization
  or basis lifting, and none states regularity under the arbitrary local map here.
- Loogle: `RingTheory.Sequence.IsRegular, Ideal.map`. Zero hits.
- LeanSearch: `A regular sequence generating an ideal in a Noetherian local ring gives
  a basis modulo the maximal ideal and any lifted basis is regular`. Eight hits,
  including `IsLocalRing.isRegular_of_perm` and `IsLocalRing.span_eq_top_of_tmul_eq_basis`.
  Permutation invariance and Nakayama generation separately do not give this theorem.
- Mathlib grep: `(lift|generat|basis).*([Rr]egular|[Cc]onormal)|([Rr]egular|[Cc]onormal).*(lift|generat)`
  under `RingTheory/Regular`: only two introductory comments in `ProjectiveDimension.lean`.
- Mathlib grep: `ResidueField|residueField|Cotangent` under `RingTheory/LocalRing`:
  existing residue-field and local-module constructions were found and reused.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for regular-generator lifting,
  residue bases and generator spaces found supporting results such as
  `FlatQuotientNestedRegularIdeals`, whose proof references this node, but no existing
  declaration of the item. The exact-node-id `grep -rn` in `lean/WeilConjectures`
  returned nothing. Final exact-name searches for
  `lift_regular_generators_through_fibre` / `LiftRegularGeneratorsThroughFibre` in
  Mathlib, both project roots and `dag/lean_names_upstream.json` returned nothing.

Validation: `scompile.py` compiled the file in sandbox and library module mode cleanly
(2.1 s and 1.8 s respectively), with no warnings. No statement fault or dispute was found.

## Second reading by Q41

(Written by the maintainer's second reader NT-cc, replacing the delivered self-check
section, which claimed no independent reading.)

Node statement as a list, with the Lean rendering and verdict:

1. $(R,\mathfrak m)$, $(S,\mathfrak n)$ nonzero commutative Noetherian local rings:
   `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
   [IsLocalRing R] [IsLocalRing S]`; `IsLocalRing` extends `Nontrivial` (nonzero). Independent
   universes. `IsNoetherianRing` is the recorded declaration of def-weil-pbc-noetherian-ring. OK.
2. $c$ local with $c(\mathfrak m)\subseteq\mathfrak n$: `c : R →+* S` `[IsLocalHom c]`
   (equivalent by `IsLocalRing.local_hom_TFAE`). OK.
3. Induced isomorphism $k\cong S/\mathfrak n$: `σ` with `hσ` fixing it on every class `[a] ↦ [c a]`;
   σ is therefore the induced map, not an arbitrary isomorphism. OK.
4. $I\subseteq\mathfrak m$ finitely generated, $J=IS$: `I`, `hI`, `hIfg`; $J$ is literally `I.map c`. OK.
5. $\beta : I/\mathfrak mI\to J/\mathfrak nJ$ the induced map, a $k$-linear isomorphism:
   `β` semilinear over `σ` on `I ⧸ (m • ⊤)` → `I.map c ⧸ (n • ⊤)`, `hβbij` bijective, `hβ` pins it on
   every representative to `[c a]`. Canonical, not arbitrary; semilinearity over σ = $k$-linearity
   when $S/\mathfrak n$ is a $k$-space through σ. OK.
6. $y_1,\dots,y_r\in\mathfrak n$ an $S$-regular sequence generating $J$: `y : Fin r → I.map c`, `hy`,
   `hyreg` (`RingTheory.Sequence.IsRegular S`, recorded declaration of def-weil-pbc-regular-sequence,
   includes $S/(y)\ne0$), `hygen`. Subtype-valued tuple adds no restriction since the $y_i$ generate $J$. OK.
7. Conclusion (a), $[y_i]$ a $k$-basis of $J/\mathfrak nJ$: rendered as ∃ basis `b` of $I/\mathfrak mI$
   over $R/\mathfrak m$ with `β (b i) = [y i]`. Since β is a bijective σ-semilinear map, this is equivalent
   to $([y_i])$ being an $S/\mathfrak n$-basis (= $k$-basis through σ) of $J/\mathfrak nJ$, in the given order. OK.
8. Conclusion (b), for every basis and every lifts: `∀ b f, (∀ i, [f i] = b i) →` span of `f` = `I`,
   `IsRegular S (List.ofFn (c ∘ f))`, span of `c ∘ f` = `I.map c`. Arbitrary basis, arbitrary lifts,
   no requirement that lifts relate to `y`. OK, not weaker or stronger.
9. Conclusion (c), existence of bases and lifts including $r=0$: third conjunct ∃ b f. OK.

Edge cases: $r=0$ (Fin 0 bases/lifts; empty sequence regular as $S\ne0$; $J=0$, $I=0$ forced
by the hypotheses, not assumed); $I=0$; fields; non-injective, non-flat $c$; different universes;
arbitrary characteristic. No extra hypothesis (no regularity of $R$/$S$, no flatness, no surjectivity).

Mathematics: Stacks 066A(1) (more-algebra.tex, lemma-independence-of-generators) read: a tuple of
length $r$ generating an ideal generated by a quasi-regular sequence of length $r$ is quasi-regular;
061S converts quasi-regular to regular in Noetherian local rings. The statement is true as stated.

Records: stmt_deps unchanged (def-weil-pbc-noetherian-ring, def-weil-pbc-regular-sequence), both
used through their recorded declarations; no statement_change; `lean.statement` is verbatim the
file signature; docstrings carry source place, `(blueprint: lem-trf-lift-regular-generators-through-fibre)`
and the six proof steps; proof is `sorry`; no definitions added; imported proof-dep modules exist in
the live tree. Searches: rg for `lift_regular_generators`, `LiftRegularGeneratorsThroughFibre` in
lean/Sheaf found nothing beyond this delivery; Mathlib regular-sequence API (`isRegular_of_perm`,
localization lemmas) only covers permutations/localization. No mismatch found; nothing changed in the Lean.
