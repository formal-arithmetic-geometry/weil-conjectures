## Worker report

The module `lean/Sheaf/AlgebraicGeometry/UnboundedSiteComparison.lean` states
`AlgebraicGeometry.ProEtale.unboundedSiteComparison`. It uses the canonical
`finiteCoefficientComparison` and `finiteCoefficientDerivedComparison` declarations from
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, rather than defining a second comparison.
The theorem records exactness as preservation of finite limits and finite colimits, full
faithfulness via `Nonempty F.FullyFaithful`, and arbitrary small direct sums as preservation
of colimits of every discrete diagram. The finite-field/algebraically-closed alternative is
`hbase : Finite k ∨ IsAlgClosed k`; invertibility is `IsUnit (algebraMap ℤ k (ℓ : ℤ))` with
`[Fact ℓ.Prime]`; finite primary coefficients are `hA : ∃ n, (ℓ : A)^n = 0`; finite type
is `[X.Over (Spec (CommRingCat.of k))]`, `[LocallyOfFiniteType ...]`, and `[QuasiCompact ...]`.
The proof is `sorry`, as required for stage 2.

The dependency declarations used are:

- `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` from
  `Sheaf.AlgebraicGeometry.DerivedCategories` (derived-category encoding dependency).
- `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and related comparison declarations
  from `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` (finite-coefficient module and derived
  comparison encoding).
- `AlgebraicGeometry.Scheme.proEtaleSiteComparison` from
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (canonical site comparison).
- `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.LocallyOfFiniteType`/
  `AlgebraicGeometry.QuasiCompact` from Mathlib (scheme and finite-type dependencies).

Edge cases checked: the zero coefficient ring, `A = ZMod (ell^n)`, the empty scheme, zero
complexes, empty discrete coproducts, and arbitrary index types including an empty index.
The theorem keeps the full unbounded derived categories and does not impose boundedness.

Searches made: `msearch.py Q67 lem-sfb-unbounded-site-comparison leanfinder` for the
unbounded etale/pro-etale comparison (generic derived-category hits only); `msearch.py ...
loogle 'Functor.FullyFaithful, PreservesColimitsOfShape'` (generic categorical declarations);
`msearch.py ... grep 'proetale|pro.etale' Mathlib/AlgebraicGeometry/Sites` (site constructions
only); `rg` over `WeilConjectures/` and `lean/Sheaf` for the item and comparison names.
The existing source comparison is bounded-below, so it does not state this unbounded result.
No new nodes or dependency modules were needed.

## Earlier second reading (a previous round; superseded)

I reread the item statement and all five statement dependencies. The field alternative, prime
invertibility, primary finite coefficient condition, scheme-over-field and finite-type
hypotheses are each represented by the corresponding binders in the theorem. The conclusion
has the three requested clauses: exactness of the comparison, full faithfulness of its
unbounded derived functor, and preservation of every discrete colimit, including the empty
index. The module compiles cleanly with the recorded signature and uses the canonical
comparison declarations from the dependency module. No statement or dependency was changed.

## Second reading by Q67

I independently opened the sandbox node and Lean module, all five statement-dependency
nodes and their recorded source signatures, the blueprint statement
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-pe-unbounded-classical/`
`sk-prop-pe-unbounded-classical-unit.md` and its proof, and the relevant Stacks text.
There is no statement_change, new definition node, or dependency module in this delivery.
No repair note for this item is present in the shared repository.

The node's objects, hypotheses and conclusion clauses, matched individually:

- Field k: `(k : Type u) [Field k]`. Same object; pass.
- Finite or algebraically closed base: `hbase : Finite k ∨ IsAlgClosed k`.
  The disjunction retains both cases and adds neither perfection nor a characteristic
  restriction; pass.
- Prime ell: `{ℓ : ℕ} [Fact ℓ.Prime]`; pass.
- Ell invertible in k: `hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ))`; pass.
- Finite commutative ring A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  No field, reducedness, or nonzero-ring assumption; pass.
- Constant discrete coefficients: `[TopologicalSpace A] [DiscreteTopology A]`.
  These specify the source's discrete ring; every finite ring has this topology,
  so this does not exclude a coefficient ring; pass.
- Annihilation by some power of ell: `hA : ∃ n : ℕ, (ℓ : A) ^ n = 0`.
  Multiplication by this scalar kills every A-module; no choice of exponent is fixed;
  pass.
- Scheme over k: `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]`.
  The recorded `AlgebraicGeometry.Scheme` is Mathlib's locally ringed space with local
  affineness. No separatedness assumption; pass.
- Finite type over k: `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]` and
  `[QuasiCompact (X ↘ Spec (CommRingCat.of k))]`. I read both Mathlib class signatures;
  their conjunction is exactly the recorded finite-type notion; pass.
- Ordinary unbounded etale category: `FiniteCoefficientEtaleDerivedCategory X A`
  unfolds to `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  This is the same fixed-ring encoding as `Etale.DerivedCategoryModule A X` in the
  recorded DerivedCategories module. It is not D-plus or the constructible subcategory;
  pass.
- Ordinary unbounded pro-etale category: `FiniteCoefficientDerivedCategory X A`
  is the ordinary derived localization of `FiniteCoefficientModules X A`, which is
  `ringedSiteModules (finiteCoefficientRingSheaf X A)`. I opened these definitions:
  the ring sheaf sheafifies `C(ConnectedComponents U.left, A)`, with restriction by
  precomposition. This is the dependency's quotient-topology construction. Its canonical
  constant-scalar local bijection identifies it with the constant discrete ring sheaf;
  pass.
- Canonical comparison: `finiteCoefficientComparison X A` is
  `comparisonUpperStar (ModuleCat A) X` followed by canonical coefficient realization.
  `finiteCoefficientDerivedComparison X A` is definitionally its `mapDerivedCategory`.
  I read `Scheme.proEtaleSiteComparison` and `proEtaleSiteComparisonModules`: the
  inclusion is `Scheme.toProEt`, with Kan extension/sheafification left adjoint and
  restriction right adjoint. No arbitrary functor or map was introduced; pass.
- Exactness ON DERIVED CATEGORIES: repaired to
  `(finiteCoefficientComparison X A).mapDerivedCategory.IsTriangulated`.
  This uses Mathlib's canonical shift-commutation structure on the same derived functor
  and means preservation of distinguished triangles. The first version concluded only
  `PreservesFiniteLimits` and `PreservesFiniteColimits` for the abelian-sheaf functor;
  that did not directly render this node's conclusion. Those two conjuncts were replaced;
  no change to the mathematical node was needed. Pass after repair.
- Full faithfulness: `Nonempty (finiteCoefficientDerivedComparison X A).FullyFaithful`.
  This is a fully faithful structure on the entire unbounded functor, without a
  cohomological lower-bound hypothesis; pass.
- Arbitrary small direct sums: `∀ (I : Type v), Nonempty
  (PreservesColimitsOfShape (Discrete I) (finiteCoefficientDerivedComparison X A))`.
  This quantifies over every index type in an independent universe and every diagram
  of that shape; there is no nonemptiness or finiteness restriction; pass.

Edge cases: A may be the zero ring; exponent n = 0 is allowed and then forces A to be
zero. Nonzero examples include Z/ell and Z/ell^2; A is not silently assumed to have
characteristic ell. A field of characteristic ell is excluded exactly by hℓ; characteristic
zero and other allowed characteristics remain. X may be empty or zero dimensional.
The comparison accepts zero objects and complexes unbounded in both directions. Empty
index types and zero summands are included. Scheme universe u is arbitrary, coefficients
and module values use the established larger site universe u+1, and the coproduct index
universe v is independent. No site object/morphism universe equality was added.

Independent searches (2026-10-17):

- `msearch.py Q67 lem-sfb-unbounded-site-comparison leansearch` with
  `unbounded derived etale proetale comparison fully faithful finite coefficients`:
  generic etale forgetful and constant-sheaf declarations, no matching theorem.
- `msearch.py ... leanfinder` with
  `etale proetale unbounded derived inverse image triangulated fully faithful coproducts`:
  generic sites, triangulated composition and `mapDerivedCategoryFactorsh`; no match.
- `msearch.py ... loogle 'CategoryTheory.Functor.mapDerivedCategory'`: found the
  exact-functor construction, its canonical CommShift and IsTriangulated instances;
  these supply the correct existing vocabulary for the repaired exactness clause.
- Direct rg searches in Mathlib AlgebraicGeometry/Sites and
  Algebra/Homology/DerivedCategory, the upstream WeilConjectures comparison files,
  shared lean/Sheaf, the 51-module pro-etale framework, dag/nodes, and
  dag/lean_names_upstream.json. The framework uses module objects over condensed
  coefficients, not this finite constant-ring comparison theorem. The closest shared
  result is `siteComparison_boundedBelow` in ProEtaleSiteComparisonDerived; it uses
  `mapDerivedCategoryPlus`. Upstream Derived/Comparison's
  `isIso_derivedComparisonAdjunction_unit_app` and
  `bijective_comparisonUpperStar_mapDerivedCategory_map` explicitly require t.plus.
  I opened these declarations; none states full faithfulness for arbitrary unbounded
  inputs. The item therefore needs its own theorem; no definition is duplicated.

Source and proof check: the blueprint assumes exactly the field/prime/finite-primary/
finite-type hypotheses above. Stacks 07K7 in derived.tex assumes enough acyclics and
vanishing of one higher derived functor; the node supplies enough injectives and the
uniform bound. Stacks 08FI in sites-cohomology.tex applies to any site object, 099W
in proetale.tex has no extra geometric hypothesis, and 07D9 in injectives.tex gives
termwise sums in Grothendieck derived categories. Their uses in the node introduce no
extra assumptions. I replaced the abbreviated proof docstring by all eight node steps:
exactness and cohomology; K-injective adjunction; localized section maps; both bounds;
fixed-degree truncation; the natural comparison square; exact sheafification; full
faithfulness and coproducts. All recorded proof-dependency modules were added as ordinary
imports, following stage-2 rule 7; dependencies without a recorded module remain named in
the proof docstring. The copyright header was supplied and autoImplicit disabled.

Compilation found that the named wrapper `finiteCoefficientDerivedComparison` does not
export a CommShift instance by typeclass search. Spelling its definitionally identical
`(finiteCoefficientComparison X A).mapDerivedCategory` in the exactness clause uses the
existing canonical shift structure directly, without a helper definition or dependency
repair. The final module passed scompile.py: sandbox 2.8 s and module 3.1 s, no errors
or warnings. Every variable and both universes are explicitly bound; the only proof is
`sorry`, no data definition was added, all lines are at most 100 characters, and
lean.statement was copied verbatim from the final theorem signature.

Delivery validation: deliver2.py --no-push passed the server preflight and compilation
(commit 667baf9f2d); the delivery contains one module, the item node, and this report.
