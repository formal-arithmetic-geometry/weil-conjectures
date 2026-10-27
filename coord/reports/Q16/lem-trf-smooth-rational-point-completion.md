# Q16 — lem-trf-smooth-rational-point-completion

## Worker report

The new module `Sheaf.RingTheory.SmoothRationalPointCompletion` states
`Algebra.essentiallySmooth_rationalPoint_completion`, with proof `sorry`.
It defines no new mathematical objects. The natural-language statement and all
nine proof steps are unchanged. The proof docstring contains all nine steps,
including the coefficient calculation, localization, inverse-limit construction,
maximal-ideal calculation, and graded multiplication calculation.

This repair retains the previously delivered statement and its nine-step proof
docstring. The independent return on immutable head `ba22da405e3e` identified one
H2/§1(A) ownership fault: a theorem node was cited solely for a plain helper
definition. The repair uses the return's expressly permitted alternative of
stating base graded compatibility on representatives and dropping that theorem
statement dependency. No definition or dependency module is added.

### Hypotheses and clauses

- The two commutative rings are `R : Type u` and `S : Type v`, with independent
  universes and `[CommRing R] [CommRing S]`.
- Nonzero local rings are `[IsLocalRing R] [IsLocalRing S]`. Mathlib's local-ring
  class already implies `Nontrivial`, so there are no duplicate instance binders.
- Noetherianity is `[IsNoetherianRing R] [IsNoetherianRing S]`.
- The given homomorphism is `algebraMap R S`, supplied by `[Algebra R S]`.
  Every homomorphism gives such a structure, so this excludes no map.
  Locality is `[IsLocalHom (algebraMap R S)]`.
- The specified common field is `(L : Type w) [Field L]`, with independent universe.
  `rR : ResidueField R ≃+* L` and `rS : ResidueField S ≃+* L` are the specified
  identifications. `ResidueField R` is the actual quotient by `maximalIdeal R`.
  `hres : ∀ a, rS (residue S (algebraMap R S a)) = rR (residue R a)` expresses
  that the given map induces the identity under these identifications. It is
  not just an assertion that the two residue fields are abstractly isomorphic.
- Essential smoothness is `hsmooth : Algebra.EssentiallySmooth R S`, exactly the
  recorded localization-of-a-smooth-algebra predicate, without adding finite
  presentation of the local map or an augmentation.
- The differential fibre is `(ResidueField S) ⊗[S] KaehlerDifferential R S`.
  This is the scalar extension of the displayed fibre over `L` under `rS`;
  dimensions and finite dimensionality are invariant under that specified field
  equivalence. The tensor order is the usual scalar-extension order, canonically
  equivalent to the node's `Ω ⊗ L`. The first conjunct is `Module.Finite` over
  this field, which is finite dimensionality, not an assumption. The existential
  natural number `s` is fixed by the next conjunct to `Module.finrank` of that
  same fibre. This retains dimension zero and does not use finrank alone as a
  substitute for the finite-dimensional conclusion.
- `e : AdicCompletion (maximalIdeal S) S ≃+*
  MvPowerSeries (Fin s) (AdicCompletion (maximalIdeal R) R)` is the displayed
  completion isomorphism. Both completions are Mathlib's actual compatible
  quotient sequences, and the power series are Mathlib's coefficient families.
- The first condition on `e` specifies the completed base map: for each `n`,
  each completed base element `x`, and each representative `a` of its `n`th
  coordinate, the `n`th coordinate of `e.symm (MvPowerSeries.C x)` is the class
  of `algebraMap R S a`. This characterizes the actual induced completion map,
  rather than an arbitrary homomorphism agreeing only on original base elements.
  Equivalently the structural map is `e.symm.toRingHom.comp MvPowerSeries.C`;
  with that canonical structure, `e` is an isomorphism of completed-base algebras.
- The next condition, for every completed `S` element, equates
  `rR (AdicCompletion.evalOneₐ _ (MvPowerSeries.constantCoeff (e x)))` and
  `rS (AdicCompletion.evalOneₐ _ x)`. This is exactly identity on the specified `L`.
- The two `IsLocalRing` conjuncts assert locality of the completed source and
  the power-series target. The two `IsAdicComplete` conjuncts assert completeness
  for their maximal-ideal topologies: the extended maximal ideal on the source,
  and the explicitly displayed ideal on the target. These are properties of
  the fixed rings, not additional hypotheses.
- The target ideal is `(maximalIdeal R).map (MvPowerSeries.C.comp (algebraMap R _))
  ⊔ Ideal.span (Set.range MvPowerSeries.X)`. This is precisely the ideal generated
  by the completed base maximal ideal and all `s` variables. Its `IsMaximal`
  conjunct, together with locality, identifies it as the maximal ideal. The
  equality `Ideal.map e.toRingHom (extended maximalIdeal S) = target ideal`
  makes the complete local compatibility explicit. A local ring isomorphism
  mapping these ideals also maps every power, hence respects both adic topologies.
- `g : MvPolynomial (Fin s) (Ideal.associatedGraded (maximalIdeal R)) ≃+*
  Ideal.associatedGraded (maximalIdeal S)` is the inverse orientation of the
  displayed associated-graded isomorphism, with exactly the same mathematical data.
- The clause `∀ (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n)
  (hb : algebraMap R S a ∈ maximalIdeal S ^ n), ...` specifies the base graded
  compatibility on representatives: `g (C (ι_n [a])) = ι_n [algebraMap R S a]`.
  Both classes are `Submodule.Quotient.mk` in the recorded
  `Ideal.associatedGradedPiece`, and both inclusions are `DirectSum.of`.
  This pins the map in every degree, including degree zero. The proof binder
  `hb` is universally quantified in the conclusion, not a new theorem hypothesis:
  the given local map takes the base maximal ideal into the target maximal ideal
  by `IsLocalRing.maximalIdeal_comap`, hence takes every power into the
  corresponding power by `pow_le_pow_left'` and `Ideal.le_comap_pow`. Thus such
  `hb` always exists. Quotient projections are surjective and the direct sum is
  additively generated by its homogeneous inclusions, so these equations are
  equivalent to the previous equality with the canonical graded additive map.
- The last condition puts every `g (MvPolynomial.X i)` in the image of
  `DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal S)) 1`.
  Thus variables have degree one; coefficient classes retain their degrees by
  the preceding canonical-map equality. By distributivity this preserves the
  total grading (coefficient degree plus monomial degree) on all polynomials.
  Its inverse is graded too: apply injectivity and the direct-sum decomposition
  to an element whose image has only one nonzero homogeneous component.
- In degree zero the canonical base map, together with `hres`, identifies the
  specified copies of `L`. Consequently `g` is an isomorphism of graded
  `L`-algebras, expressed by ring equivalence and the explicit scalar/base equations
  rather than by installing an additional transported algebra instance.

There is no statement correction, dispute, or omitted clause.

### Dependencies used

The recorded statement dependencies are used directly:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (every ideal finitely
  generated; `isNoetherianRing_iff_ideal_fg` gives the definition's ideal formulation).
- `WeilConjectures.RingTheory.EssentiallySmooth`: `Algebra.EssentiallySmooth`.
  Read its full existential definition and docstring, including the localization
  convention and the local-ring specialization.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, with its universal
  derivation `KaehlerDifferential.D` and universal property
  `KaehlerDifferential.linearMapEquivDerivation`.
- `Mathlib.RingTheory.AdicCompletion.Algebra` (extends the recorded Basic module):
  `AdicCompletion`, `AdicCompletion.evalₐ`, `AdicCompletion.evalOneₐ`, and
  `IsAdicComplete`. Their types specify actual quotient evaluation and completeness.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`, `constantCoeff`.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, and its commutative ring structure. This is the
  recorded direct sum of the actual quotients of successive ideal powers.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, its constant homomorphism
  `C` and variables `X`; the recorded evaluation/universal-property declarations
  `MvPolynomial.aeval` and `MvPolynomial.algHom_ext` were inspected too.

The repaired module does not import `Sheaf.RingTheory.FormallyEtaleAssociatedGraded`
and does not reference `Ideal.associatedGradedMap` or its two helpers.
`lem-sfb-augmented-etale-associated-graded` is removed from the packet's `stmt_deps`;
the remaining list is exactly the current main-branch list. The existing
associated-graded-ring definition supplies every object needed for the explicit
representative formula. No new notion needs ownership.

Proof imports retain the already stated proof dependencies: the smooth/affine
and étale/affine equivalences, étale local normal form, differential comparison,
polynomial differential basis and differential localization, locally Noetherian
finite type result, localization Noetherianity and flatness, smooth/étale
flatness, flatness over a localization, unramified maximal-ideal comparison,
flat-local completion isomorphism and completion modulo ideal powers. These are
plain imports, as prescribed for proof dependencies. No proof is supplied here.

### Edge cases

For `s = 0`, `Fin s` is empty, the variable span is zero, and both polynomial
and series rings reduce to their coefficient rings. For `R = L` a field, its
maximal ideal is zero and the statement gives the usual power series and polynomial
tangent cone. Nilpotents in a nonreduced base are retained by the coefficient rings;
there is no domain, regularity, or reducedness hypothesis. Mixed characteristic
is allowed: neither a field structure on `R` nor a coefficient-field section
`L → R` is used. The specified residue maps are checked in degree zero, and the
completion coordinate formula includes `n = 0` (the zero quotient), as well as
all positive powers. Arbitrary independent universes `u v w` are retained.

### Searches and source checks

All three prescribed search kinds were run through `batch2/msearch.py`:

1. LeanFinder: `essentially smooth local homomorphism identical residue fields
   completion power series associated graded polynomial` — eight hits, including
   Weierstrass preparation, local standard smoothness, and one-variable residue
   fields; no theorem with these two conclusions and these hypotheses.
2. Loogle: `AdicCompletion, MvPowerSeries, AlgEquiv` — three hits, the
   `MvPowerSeries.toAdicCompletionAlgEquiv` theorem and its application lemmas.
   That theorem completes only at the variable ideal over an uncompleted base,
   so it is not the present theorem.
3. Mathlib grep: `smooth.*[Cc]ompletion|[Cc]ompletion.*[Ss]mooth|
   [Aa]ssociatedGraded.*[Pp]owerSeries` in `RingTheory` — five hits about
   formal smoothness and adic lifting, not the required completion presentation.

Searched both `lean/WeilConjectures` and `lean/Sheaf` by the exact blueprint id,
by smooth/completion patterns, and by associated-graded map/polynomial patterns.
The augmented smooth-completion theorem needs an augmentation and uses its kernel
as completion ideal; this item supplies no such augmentation. The existing
`RingHom.flat_local_completion_iso` is the étale-chart input, with different
hypotheses and no power-series or graded conclusion. The existing
`Ideal.associatedGradedMap` was inspected; the repaired signature states its
representative characterization without referencing or redefining that helper.
An exact-name search in both Lean trees and `dag/lean_names_upstream.json` found no declaration named
`essentiallySmooth_rationalPoint_completion`.

Read the local Stacks sources at `morphisms.tex`,
`lemma-smooth-etale-over-affine-space` (054L), and `more-algebra.tex`,
`lemma-flat-unramified` (0AGX), including their proofs. They give precisely the
étale polynomial chart and the induced completion isomorphism used in the node.
The nine-step node proof supplies the intervening coefficient and graded calculations.

### Validation

Only `scompile.py` is used for compilation. The first compile succeeded but
reported overlapping `Nontrivial`/`IsLocalRing` instances; removed the redundant
`Nontrivial` binders without changing the hypotheses. The final file has explicit
universe binders, `set_option autoImplicit false`, module mode, public statement
imports and one theorem with `sorry` as its entire proof. Every line is at most
100 characters. The node record's statement is copied verbatim from the signature.
The previous delivery passed server compilation and preflight, but the
independent review subsequently found the ownership defect described above.
This repair first ran the required dry run on the saved packet, then changed the
graded compatibility signature and dependency list. The repaired module passed
`scompile.py` with no warnings or errors: sandbox 14.5 s, library 11.1 s.
The self-check verified that the only node-field delta from current main is
`lean`, the stored signature matches verbatim, the removed helper/import is
absent, all Lean lines are at most 100 characters, and the sole proof is `sorry`.
The final delivery dry run is required to pass before pushing.

## Second reading by Q16

No independent worker reading is claimed. Per the current dispatcher brief,
the worker delivers directly and the maintainer supplies the independent review.

## Repair of return L (H2/§1(A))

Selected the return's second alternative: state the base graded compatibility on
representatives and drop the theorem statement dependency. The module's sole
changed mathematical clause is the equivalent equation on every homogeneous
representative. The theorem import and added dependency are removed, the node's
`lean.statement` is regenerated verbatim, and no other node field differs from
current main. No statement correction is needed: the natural-language statement,
proof, and proof dependencies are unchanged.

The self-check reads the node against the full signature. The supplied local map
still determines the image of every representative, rather than introducing an
arbitrary graded map. For `n = 0`, both power ideals are top and the formula fixes
the quotient residue map; with `hres` this is the specified identity on `L`.
For `n > 0`, locality gives membership of the image in the target power. Different
membership proofs yield identical subtype terms by proof irrelevance. When a
representative lies in the next power, both quotient classes vanish, since the
same local map preserves that next power. Empty variables (`s = 0`), a field base,
nonreduced rings, and mixed characteristic are still covered. The new clause uses
only the original independent universes and introduces no new assumptions.
