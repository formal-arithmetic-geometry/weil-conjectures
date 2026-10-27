## Worker report

The module `Sheaf.TraceFormula.DepthFittingQuadraticLCI` states
`Algebra.depth_fitting_quadratic_lci`, with its sole proof `sorry`, and supplies the
transparent abbreviation `Algebra.BinaryQuadraticQuotient` for precisely the
binary quadratic power-series quotient occurring in the conclusion. The
abbreviation has real data, introduces no choice, and is a helper belonging to
this node's displayed construction. No new notion node or dependency repair is
needed. The node is changed only in `lean`.

Hypothesis and conclusion correspondence:

- The field and finite type algebra are `{k : Type u} {S : Type v} [Field k]
  [CommRing S] [Algebra k S] [Algebra.FiniteType k S]`. The recorded
  `RingHom.FiniteType (algebraMap k S)` is definitionally this same finite-type
  property of the specified algebra structure.
- The maximal ideal is `(p : Ideal S) [p.IsMaximal]`; `Localization.AtPrime p`
  is A. Its `IsLocalRing.maximalIdeal` is precisely pA.
- F is `p.ResidueField`, the quotient of A by its maximal ideal. For a maximal
  p the canonical algebra map `(S ⧸ p) → p.ResidueField` is bijective, by
  `Ideal.bijective_algebraMap_quotient_residueField`. Thus this is the canonically
  identified S/p, not a field chosen independently or an additional hypothesis.
- F/k finite separable is `[FiniteDimensional k p.ResidueField]
  [Algebra.IsSeparable k p.ResidueField]`. There is no perfectness or
  characteristic restriction.
- `hdepth` is `IsLocalRing.depth (R := Localization.AtPrime p)
  (Localization.AtPrime p) = 1`.
- The index-one Fitting ideal is `π.presentationFittingIdeal 1`, where
  `π : (Fin n → S) →ₗ[S] KaehlerDifferential k S` is any surjection (`hπ`).
  This displays the finite presentation used in the node's definition of its
  presentation-minor ideal. Differentials are finitely generated for finite type
  algebras, so such a presentation always exists. Quantifying over an arbitrary
  one is equivalent to the intrinsic ideal condition by the recorded
  `LinearMap.presentationFittingIdeal_independence_baseChange`; it is not a
  freeness assumption on differentials or a restriction on the presentation.
- `hfitting` maps that ideal by `algebraMap S (Localization.AtPrime p)` and
  equates it to the maximal ideal of A, exactly Fit_1(Omega)A = m.
- The completion is the actual Mathlib
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
  (Localization.AtPrime p)` throughout.
- The existential `σ : p.ResidueField →ₐ[k] AdicCompletion ...` is a k-algebra
  map; `∀ z, AdicCompletion.evalOneₐ ... (σ z) = z` says it is a section of
  the canonical residue map. Nothing is chosen through an unproved existence
  theorem.
- `∃ (a b c : p.ResidueField), b ^ 2 - 4 * a * c ≠ 0` is exactly the specified
  quadratic nondegeneracy condition, including characteristic two.
- `e : AdicCompletion ... ≃+* BinaryQuadraticQuotient a b c` is an actual ring
  equivalence to F[[u,v]]/(a*u^2+b*u*v+c*v^2), with variables `Fin 2` indexed by
  0 and 1. The equation `∀ z, e (σ z) = algebraMap p.ResidueField _ z`
  makes this exactly an F-algebra equivalence when F acts through σ: for any
  x, multiplicativity gives e(σ(z)*x) = z*e(x). This avoids selecting an
  unrelated F-action or hiding an instance in a let-binder. Since σ is a
  k-algebra map it also gives the required k-compatibility.
- Both `@Continuous` clauses use explicit `Ideal.adicTopology` instances. On
  the completion the ideal is the image of m; on the quotient it is the image
  under `Ideal.Quotient.mk` of the ideal spanned by X_0 and X_1. These are the
  maximal-ideal and quotient-variable-ideal topologies, respectively. The
  inverse is continuous too. Completeness and locality of both rings follow
  from their actual constructions (A is Noetherian local, and the binary
  quotient is a quotient of complete Noetherian local F[[u,v]]).
- The equation for every power series f,
  `evalOneₐ ... (e.symm (Ideal.Quotient.mk _ f)) = constantCoeff f`, explicitly
  requires identity on the residue F. Constant compatibility and locality imply
  this equation, so this spells out the node's normalization without imposing
  an additional mathematical restriction.
- The independent final conjunct is `∃ g : S, g ∉ p ∧
  IsLocalCompleteIntersection k (Localization.Away g)`, exactly the principal
  LCI neighbourhood assertion. The localization finite-type instance is supplied
  by `Mathlib.RingTheory.Localization.Away.AdjoinRoot`.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField` and
  `Ideal.bijective_algebraMap_quotient_residueField`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, `AdicCompletion.evalOneₐ`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal
  derivation and `linearMapEquivDerivation`.
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal` and its independence/base-change theorem.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`,
  `constantCoeff`; `Mathlib.GroupTheory.MonoidLocalization.Away`:
  `Localization.Away`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection` and `IsGlobalCompleteIntersection`.
- `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`: `Ideal.adicTopology`.

The modules of all recorded proof dependencies are imported with plain imports:
separable closed-point formal presentation; localized differentials
(`KaehlerDifferential.isLocalizedModule_map`); completion faithful flatness
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`, with completion flatness/locality);
`IsLocalRing.depth_eq_add_of_flat_local`; the formal Jacobian quadratic criterion;
power-series no-zero-divisors; regular sequences; and
`Algebra.completion_local_complete_intersection_iff`. The docstring gives all
five proof steps and their DAG citations. No imported proof is redeclared.

Edge cases checked before drafting: the zero ring S has no maximal p; a field
local ring has depth zero, so does not meet hdepth; a smooth one-dimensional
point has unit Fit_1 rather than m, so does not meet hfitting. In characteristic
two the discriminant is b^2, so b nonzero is the correct polar nondegeneracy
condition and no division by two occurs. The split node a=c=0,b=1 is included
in every characteristic. Arbitrary finite generating surjections, including
n=0,1, use the existing Fitting convention n≤1 ⇒ unit ideal, which cannot equal
m. No universe equality between k and S is imposed; all universes and variables
are explicitly bound. The coefficient field can be any finite separable residue
extension, including the trivial extension.

Source read: `literature/stacks-project/curves.tex`, lemma-fitting-ideal (0C4C),
lemma-nodal (0C4D), and the final complete-intersection paragraph of
lemma-nodal-lci (0C4E). This agrees with the node; no correction or dispute arose.

Searches made with the prescribed `msearch.py` wrapper:

- LeanFinder: "A finite type algebra of depth one and maximal first Fitting ideal
  of differentials has nondegenerate binary quadratic completion and a local
  complete intersection neighbourhood". Eight hits: smoothness, standard
  smoothness, submersive presentations, smooth/etale loci. None states the
  depth/Fitting quadratic-completion criterion or the LCI conclusion.
- Loogle: `MvPowerSeries, KaehlerDifferential`. Zero hits.
- Mathlib grep in `RingTheory`:
  `Fitting|fittingIdeal|quadratic.*completion|completion.*quadratic`. Only two
  hits, both the unrelated Fitting decomposition in Artinian/Module.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `depth_fitting|fitting.*quadratic|quadratic.*lci|lem-trf-depth-fitting-quadratic-lci`.
  No hits. The exact new declaration names were also searched in both project
  roots and `dag/lean_names_upstream.json`, with no collision. A broader search
  for existing binary/quadratic quotient definitions found no such helper.

Validation: the prescribed scompile.py compiled the file both as a sandbox
module and as `Sheaf.TraceFormula.DepthFittingQuadraticLCI`, cleanly (2.4s and
2.0s). The initial check identified the missing finite-type localization import;
adding its defining Mathlib module resolved it. No compiler warning remains.

## Second reading by Q24

Reopened the node and module for a second clause-by-clause pass, matching the
hypotheses, section, discriminant, F-action, continuity, residue normalization,
and LCI conjunct as listed above. In particular the two continuity instances
refer to the quotient variable ideal and the extended maximal ideal, not a
coefficientwise topology; the section uses the canonical evalOne residue map;
and no arbitrary residue-field isomorphism is substituted. The helper expands
to the same polynomial as the formal Jacobian dependency. No mathematical
mismatch was found and no statement change was made. This was a second pass by
the same dispatched worker, not a claim of an independent second agent; the
brief forbids starting agents and assigns independent review to the maintainer.
