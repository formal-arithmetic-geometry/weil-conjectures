## Worker report

The module `Sheaf.Paper.StratumPerfectUniformBounds` states
`AlgebraicGeometry.ProEtale.StratumPerfectBounds.stratum_perfect_uniform_bounds`.
Its proof is `sorry`; its four other declarations are transparent abbreviations and
an explicit proposition packaging the local-model assertion, with real bodies.
There is no construction chosen from an unproved existence statement.

The source read is the current `literature/blueprint/latest/blueprint/` file
`sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md`,
paragraph (2), together with all eight proof steps of the assigned DAG node.
The assigned node specifically requires ordinary uncompleted categories for integral
coefficients; no derived-completeness premise is introduced.

Hypothesis and clause correspondence:

* The prime is `ℓ` with `[Fact ℓ.Prime]`. The field and positive characteristic are
  `k`, `[Field k]`, `[CharP k p]`, `_hp : 0 < p`; `_hpl : p ≠ ℓ` is exactly the
  characteristic exclusion.
* `Λ`, `[MonObj Λ]`, and `[IsCommMonObj Λ]` are the condensed commutative ring.
  `_hΛ` lists precisely finite discrete commutative rings (all of them, without an
  ell-primary restriction), the integer rings of finite intermediate extensions,
  those finite extensions themselves, and `Profinite.padicAlgClRingObj ℓ`.
  Ring-object isomorphism allows any representation of the stated coefficient.
  The last coefficient is the finite-subextension-valued sheaf required by
  `sk-def-sfb-qlbar-condensed`, not the larger all-continuous-functions sheaf.
  The base field as a degree-one finite intermediate extension includes Z_ell and
  Q_ell. The fixed `PadicAlgCl` represents the chosen algebraic closure up to its
  coefficient-preserving isomorphism, without a restriction on the ring's model.
* `X.Over (Spec (.of k))` supplies the k-structure, and the `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` hypotheses say separated finite type.
  `a : S ⟶ X` and `[IsImmersion a]` are exactly a locally closed immersion, including
  nonreduced strata. Its induced k-structure is the explicit composite with the
  structure map of X.
* The first three conclusions are `IsNoetherian S`, `CompactSpace S`, and
  `QuasiSeparatedSpace S`. The following existential gives finitely many affine
  opens covering every point. The next three conjuncts say S is separated finite
  type over k, and the following three say a is separated finite type.
* `Assertion Λ S` quantifies over Q in the ordinary unbounded derived category of
  `Modules Λ S`, the specified pro-etale cover, and its specified scalar complexes F.
  `Scalars Λ` is literally the existing internal-module encoding of ordinary
  modules over `scalarRingObj Λ = Λ(*)`. `Modules Λ T` is the existing internal-module
  category over `condensedRingObj Λ T`, not a new kind of sheaf.
* The cover index lives in an independent arbitrary universe `i`; the finite
  refinement still has index `Fin n`. Thus no size bound is added to the supplied
  cover. The first hypothesis on F gives a finite degree interval on each chart. Its
  second hypothesis expresses finite projectivity as a retract of a finite free
  ordinary scalar module. This is exactly the finite-projective characterization,
  expressed in internal abelian-group modules; it adds neither a choice of basis
  nor freeness. `Mod.finiteFree` is the existing library's finite direct sum.
* The third hypothesis is the local derived representing isomorphism. `realized`
  applies the recorded `finiteConstantScalarExtension Λ T` termwise; its scalar map
  is the canonical counit map from constant Λ(*) to Λ_T. No arbitrary map or
  scalar-realization functor is hypothesized.
* The existential `n, α, V, r, s` selects affine open charts inside members of the
  supplied cover. `Presieve.ofArrows ... ∈ Scheme.proetalePrecoverage.coverings S`
  is the actual fpqc/pro-etale covering condition, not mere joint surjectivity.
  `F (α j)` retains the very same scalar complex; `r ≤ s` and the following term
  vanishing give one interval for all retained complexes. The next conjunct
  retains their representing isomorphisms on the refined charts.
* For every `j, q`, `Mod.IsFinitelyPresented (scalarRingObj Λ)` is finite presentation
  of the scalar cohomology module (a finite matrix presentation of ordinary modules).
  The displayed `Nonempty (... ≅ ...)` is exactly
  H^q(Q)|V_j ≅ Λ_V_j tensor_R H^q(F_(α j)). The chosen model functor forms
  constant sheaves before extending scalars; it is not extension from an arbitrary
  condensed module. The next conjunct gives global H^q(Q)=0 outside [r,s].
* For every module N, without flatness or finiteness restrictions, the tensor
  isomorphism has left side the restriction of `Q ⊗ N[0]` in the derived category
  and right side `DerivedCategory.Q.obj` of the ordinary tensor complex of the
  retained realization with restricted N[0]. Thus this is a derived isomorphism,
  not just an assertion about separate cohomology groups.
* The next conjunct is the global vanishing for every tensor test N outside the
  same [r,s], chosen before N. Exact restriction also gives the vanishing on
  every refined chart. `HasFiniteConstantLocalModel` for each H^q(Q) states
  constructibility on the single stratum S; the explicit refined-chart formulas
  above supply these models on the same cover. `constantModelBoundedConstructible`
  is Dbc, and `DerivedCategory.torAmplitudeIn ... r s Q` is the recorded relative
  Tor amplitude. Their conjunction is precisely membership in Dctf by its
  recorded definition, with this particular interval.
* `IsEmpty S → n = 0 ∧ r = 0 ∧ s = 0` retains the empty-scheme boundary case.
  There is no nonemptiness premise anywhere in the theorem.

Dependency declarations read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; this records
  the ambient ring-object encoding reexported here.
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, `padicIntegersRingObj`,
  and the subfield continuous-function coefficients. The full constructions and
  their docstrings were read, including the finite-subextension restriction.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and the canonical point pullback.
* Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology,
  `Scheme.proetalePrecoverage`, and `ProEt.mk`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the node's constructible/Tor-amplitude interface explicitly permits the exact
  equivalent internal module encoding, used throughout this module.
* Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, its
  localization Q and the existing homology functors.
* `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarSections`,
  `scalarRingObj`, `scalarConstant`, `scalarCoefficientHom`,
  `finiteConstantScalarExtension`, `HasFiniteConstantLocalModelOnCover`, and
  `finiteConstantLocalModel_iff_exists_cover`. The canonical scalar extension is
  reused directly. `realized` supplies its additive instance through the existing
  public point-pullback colimit adjunction, composition and mapMod colimit instances,
  and the existing theorem that a finite-colimit-preserving functor is additive.
  It uses no private declaration, no new theorem or axiom, and no additional premise.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` and its k-scheme hypotheses were read
  to check the recorded setting interface. This lemma needs only that setting's
  geometry, not a chosen compactification.
* Mathlib: `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`,
  `IsLocallyNoetherian`, `IsNoetherian`, `CompactSpace`, `QuasiSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, and `IsProper` were read.
  Only the geometric properties asserted by this node occur in its conclusion.
* `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`. As the input is a specified complex,
  boundedness and its finite-projective terms are stated explicitly rather than
  replacing the specified complex by an existential perfect representative.
* Mathlib `Module.FinitePresentation` and the library's exact internal ordinary
  module counterpart `Mod.IsFinitelyPresented`: both are finite presentations,
  with the latter's definition giving a finite matrix cokernel.
* `Sheaf.Paper.ConstantModelTorAmplitude` and
  `Sheaf.Paper.CondensedConstantConstructibility`: `constantModelBoundedConstructible`,
  `HasFiniteConstantLocalModel`, `ConstantModelConstructibleFiniteTor` and
  `DerivedCategory.torAmplitudeIn`; their underlying uncompleted derived tensor
  is the existing module-object derived tensor.

All currently recorded proof-dependency modules are imported as proof imports.
`lem-sfb-admissible-scalar-model-cohomology` had no recorded Lean declaration when
read; it is a proof dependency only, so this statement does not require an added
interface for it. No proof of it is postulated inside a definition here.

Edge cases checked before writing: empty S and an empty original cover; zero
complexes and rank-zero retracts; arbitrary local intervals (including reversed
initial endpoints, which can be enlarged); disconnected S with different chart
bounds; nonreduced S; a finite ring such as Z/4 with multiplication-by-2
complex and nonprojective cohomology; integral torsion cohomology; the finite-
subextension-valued algebraic-closure coefficient; and completely arbitrary,
possibly nonflat and non-finitely-generated tensor test modules. No flatness of
scalar cohomology or of the tensor test is claimed.

Searches for an existing statement:

* `msearch.py ... leansearch` with “bounded finite projective scalar complexes
  pro etale uniform Tor amplitude constructible cohomology”: eight hits, including
  general bounded representatives and projective dimension, but no matching theorem.

* `msearch.py ... leanfinder` with “A locally scalar bounded finite projective
  complex on a pro-etale stratum has uniform cohomology and Tor bounds”: eight
  unrelated hits, including K-projective complexes and ring-theoretic finite
  presentation; no uniform stratum statement.
* `msearch.py ... loogle` with `DerivedCategory.torAmplitudeIn, Module.Projective`:
  zero hits; the service did not know the project-specific Tor-amplitude name.
* `msearch.py ... grep` with `uniform.*bound|stratum.*perfect` in AlgebraicGeometry:
  no Mathlib hits.
* `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `stratum_perfect_uniform_bounds`, `StratumPerfectBounds`, uniform Tor phrases,
  and scalar perfect refinements found the refinement theorem and the different
  quasi-coherent-space theorem, but no assertion of this node. The existing
  internal-Hom dual model theorem treats a dual as well, assumes more restrictive
  finite coefficients, and uses a different algebraic-closure coefficient; it
  is not this statement.

No node statement correction, disputed statement, new node, or dependency-record
repair is needed.

## Second reading by Q110

This section was written by the maintainer's second reader (review of delivery
c8ba1159), replacing the worker's self-check, which stated that no second agent had read
the delivery. The Lean module, the item node record and the worker report above are unchanged.

Node statement as a list, with the Lean that renders it and the verdict.

Objects and hypotheses:

1. Prime ell, the algebraic closure, E/Q_ell finite with ring of integers. In the Lean these are
   `ℓ` with `[Fact ℓ.Prime]`, the fixed `PadicAlgCl ℓ` and `E : PadicAlgCl.FiniteIntermediateField ℓ`.
   Correct.
2. Admissible Gamma: finite discrete commutative rings, O_E, E or Qbar_ell, regarded as condensed
   rings. In the Lean, `Λ` is a commutative ring object with `_hΛ`, a disjunction up to `Mon`
   isomorphism. Its four cases are `cartesianFinitePointRing A` (A finite, no ell-primary
   condition), `padicIntegersRingObj ℓ E`, `continuousMapRingObj E` and `padicAlgClRingObj ℓ`
   (the finite-subextension sheaf of sk-def-sfb-qlbar-condensed). Z_ell and Q_ell are covered
   by E = Q_ell. This is the same list as the landed `CartesianUntwistedAssertions` and
   `ScalarModelImmersionExtensionAssertions`. Correct.
3. Gamma_T = p_T^* Gamma on the small pro-etale site, with uncompleted unbounded derived
   categories. The Lean uses `Modules Λ T`, which is `Mod (Sheaf (ProEt.topology T) Ab)
   (condensedRingObj Λ T)`; `condensedRingObj` is the recorded declaration of
   sk-def-sfb-pulled-back-coefficients. The derived category is Mathlib's `DerivedCategory`,
   with no completeness condition. This internal-module encoding is the one used by the
   recorded Dctf notions of det-def-sfb-constructible-tor-amplitude. Correct.
4. Field k of characteristic p > 0 with p ≠ ell. In the Lean: `[Field k] [CharP k p]`,
   `0 < p` and `p ≠ ℓ`. Correct.
5. X separated of finite type over k. In the Lean: `X.Over (Spec k)` with
   `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` of `X ↘ Spec k`. Correct.
6. a : S → X a locally closed immersion with the induced k-structure. In the Lean:
   `[IsImmersion a]`, with the structure map of S given by the composite
   `a ≫ (X ↘ Spec k)`. Nonreduced S is allowed. Correct.
7. Q ∈ D(Gamma_S) with a specified pro-etale covering on which Q is the termwise scalar
   realization of bounded finite-projective R = Gamma(*)-complexes. In the Lean,
   `Q : DerivedCategory (Modules Λ S)`; `𝒰 : Scheme.Cover.{i} Scheme.proetalePrecoverage S`
   with an index universe that is not restricted; and `F i : CochainComplex (Mod Ab
   (scalarRingObj Λ)) ℤ`. Each `F i` is bounded, each term is a retract of
   `Mod.finiteFree _ m` (that is, finite projective), and `Q|_{U_i} ≅ Q(realized (F i))`.
   `realized` is the recorded canonical `finiteConstantScalarExtension` of
   det-def-sfb-constructible-local-model, applied termwise. It is not an arbitrary map.
   Correct. The specified complex is kept, rather than the existential
   `IsPerfectRingComplex`, because the node retains these very complexes.

Conclusions:

8. S is Noetherian and qcqs, has a finite affine open cover, and is separated of finite type
   over k; a is separated of finite type. In the Lean: `IsNoetherian S`, `CompactSpace S`,
   `QuasiSeparatedSpace S`, `∃ m (U : Fin m → S.Opens)` affine and covering, then LOFT, QC and
   IsSeparated of both the composite and `a`. All the clauses are present. Correct.
9. A finite affine pro-etale covering {V_i → S} that refines the given covering and retains the
   Q_i, together with r ≤ s and Q_i^q = 0 outside [r,s]. In the Lean: `n`, `α : Fin n → 𝒰.I₀`
   and affine opens `V j` of `𝒰.X (α j)`. The composites form a covering in
   `Scheme.proetalePrecoverage.coverings S`, which is the fpqc/weakly-etale condition and not
   only joint surjectivity. The Lean also has `r ≤ s`, term vanishing for `F (α j)`, and the
   representing isomorphism on each V_j. The quantifier order puts r and s before every N.
   Correct.
10. H^q(Q)|_{V_i} ≅ Gamma_{V_i} ⊗_R H^q(Q_i), with H^q(Q_i) finitely presented. In the Lean:
    `Mod.IsFinitelyPresented (scalarRingObj Λ)`, the finite matrix cokernel (the same encoding
    as the landed `HasFiniteConstantLocalModel`), and
    `upperStar (H^q Q) ≅ finiteConstantScalarExtension (H^q F)`. Correct.
11. H^q(Q) = 0 outside [r,s]. This is the global clause in the Lean. Correct.
12. For every Gamma_S-module N in degree 0:
    (Q ⊗^L N)|_{V_i} ≅ (Gamma_{V_i} ⊗_R Q_i) ⊗ N|_{V_i}. In the Lean, the left side is the
    derived tensor of `D(Modules Λ S)`, the same tensor as in `torAmplitudeIn`, restricted by
    `mapDerivedCategory`. The right side is `Q.obj` of the ordinary total tensor of complexes
    `realized F ⊗ single₀ (N|_V)`. N is arbitrary. This is an isomorphism in the derived
    category, which agrees with the 2026-10-21 rule on derived forms. Correct.
13. The cohomology of the tensor vanishes outside [r,s]. The Lean states it globally for every
    N, which implies the vanishing on each chart by exact restriction. Correct.
14. Bounded cohomology constructible on the single stratum, Tor amplitude in [r,s] and
    Q ∈ Dctf(S,Gamma). In the Lean: `HasFiniteConstantLocalModel` for every H^q(Q),
    `constantModelBoundedConstructible Λ S Q` and `torAmplitudeIn _ r s Q`. Together these are
    exactly membership in `ConstantModelConstructibleFiniteTor`, which is bounded
    constructible ⊓ finite Tor amplitude, with the stated interval. Correct.
15. Empty S: the cover may be empty and r = s = 0. In the Lean:
    `IsEmpty S → n = 0 ∧ r = 0 ∧ s = 0`, which is satisfiable (the empty family covers the
    empty scheme). There is no nonemptiness premise. Correct.

Edge cases: empty S and an empty `Fin 0` refinement. Zero complexes, and rank-zero retracts
(`finiteFree 0 = 0`). Local intervals that differ between charts (handled by the global min and
max). Finite rings such as Z/4 with non-projective cohomology (finitely presented, since a
finite ring is Noetherian). O_E, E and Qbar_ell, where Gamma(*) is Noetherian or a field.
Arbitrary non-flat N. Universes: k, X and S are in u, the coefficients are in
`Ab.{u+1}` over `Profinite.{u}`, and the cover universe `i` is free. Nothing is left unbound.

Searches: rg over side-live `lean/Sheaf` and `lean/WeilConjectures` for
`StratumPerfect`, `stratum_perfect`, `uniform.*Tor` and `torAmplitudeIn`. This found no other
statement of this node. The landed refinement theorem `finite_scalar_perfect_refinement` is
only the cover step, in the SheafOfModules encoding. The worker's LeanSearch, LeanFinder,
Loogle and grep searches are recorded above.

Records: only the item's `lean` field changed against side-live. `lean.statement` is verbatim
the signature in the file. The stmt_dep modules are imported publicly where they are used, and
the stated proof-dependency modules plainly (brief-stage2 §3). The four helpers are transparent
abbreviations of existing categories, a termwise canonical functor, and the conclusion `Prop`;
none of them is hollow. The only proof is the `sorry` of the theorem.

Advisory only: `CondensedRing.upperStar`, `Mod.finiteFree` and `Mod.IsFinitelyPresented` are
published framework declarations that are not attached to a stmt_dep record. They have the same
usage as the landed `HasFiniteConstantLocalModel`.

Nothing in the Lean was changed.
