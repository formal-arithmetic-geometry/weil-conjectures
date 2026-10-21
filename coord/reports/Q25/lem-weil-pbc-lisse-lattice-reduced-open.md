## Worker report

The module `Sheaf.Paper.LisseLatticeReducedOpen` states
`AlgebraicGeometry.ProEtale.exists_lisse_lattice_reduced_open`, with proof `sorry`.
No definitions or auxiliary theorems are introduced. The original node statement,
statement dependencies, and proof are unchanged. There is no statement dispute.

Source checked: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
first paragraph, printed p.61, together with Proposition 6.8.4(6) and Definition
6.8.10. Also read Stacks `etale-cohomology.tex`, lemma-etale-stratified-finite,
Tag 03S0. The full eight-step node proof is rendered in the theorem docstring:
restriction, etale-local lattice, affine member and open image, finite
stratification and extraction of an open, reduced-source scheme factorization,
finite-etale base change, and finite-etale descent with quasi-compactness.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]`. No arbitrary topology or completeness assumption
  is imposed on E. `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)`
  carries precisely the canonical extended p-adic absolute value topology.
* A=O_E: `latticeCoefficientIntegers l E` is the already defined integer subring
  transported to this `WithAbs` field. The introduced uniformizer is the existing
  `Padic.coefficientExtensionUniformizer l E`; no conclusion or hypothesis uses
  its value, so it is not an additional independent argument.
* Scheme: `(X : Scheme.{u})`. Noetherian: `[IsNoetherian X]`, which Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies with the exact finite
  affine noetherian-ring-cover convention in the node.
* Finite dimension: `_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n`. Mathlib defines
  this dimension using the supremum of strict chain lengths in irreducible
  closed subsets; this is the node's convention.
* Ell invertible on X: `_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`.
* Nonempty and reduced: `[Nonempty X] [IsReduced X]`. The latter is Mathlib's
  sectionwise reducedness, equivalent to reduced stalks by the recorded dependency.
* Small pro-etale sites and continuous coefficients: `latticeModuleRing X K`
  uses `Scheme.ProEt.topology X`, with section ring `ULift C(|V|,K)`, pointwise
  operations, and precomposition restrictions. The lift only sets the universe.
  Sites retain object universe u+1 and morphism universe u.
* The rational module L: `ringedSiteModules.{u + 1} (latticeModuleRing X K)`.
  This is transparently the existing `SheafOfModules` category.
* Pro-etale locally free of finite, possibly varying or zero rank:
  `_hL : L.IsFiniteLocallyFree`. Its actual definition is local free generating
  data with a finite family on each member of the covering, with no fixed rank.
* A nonempty quasi-compact open immersion: `∃ U : X.Opens, Nonempty U ∧
  QuasiCompact U.ι ∧ ...`. `U.ι : U.toScheme ⟶ X` is the canonical open immersion;
  representing an open immersion by its image open loses no case. Since X is
  noetherian U is also quasi-compact as a space, in addition to the explicitly
  asserted quasi-compactness of the morphism.
* Integral module on U: `M : ringedSiteModules.{u + 1}
  (latticeModuleRing U.toScheme (latticeCoefficientIntegers l E))`.
* M pro-etale locally free of finite rank: `M.IsFiniteLocallyFree`, again allowing
  variable ranks and rank zero.
* S_U(M) is the recorded sheafified scalar extension:
  `SheafOfModules.changeOfRings.{u, u+1, u+1}
  (integralLatticeCoefficientMap U.toScheme l E) M`.
* The conclusion is an isomorphism, expressed by `Nonempty (... ≅ ...)`, to
  `continuousModulePullback U.ι K L`. For an open immersion the canonical map
  j⁻¹ E_X → E_U is an isomorphism (the continuous functions on each object agree).
  Thus this ringed pullback is j⁻¹ L as an E_U-module, exactly the interpretation
  explicitly used in node proof steps 1, 7 and 8, rather than a pullback along
  constant discrete coefficients. No arbitrary map or choice of comparison is used.
* The paragraph defining continuous-constructible integral modules is background
  notation, not a hypothesis or an extra conclusion: the node's actual conclusion
  asks for a lisse integral M_U. The definition remains available by public import
  of `ContinuousConstructibleModule` and is not redefined or imposed on L.

Dependency declarations inspected and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly retains
  `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`, and
  `coefficientExtensionUniformizer`; the primary recorded finiteness theorem was
  read, but its finite quotient is not needed for this signature.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` retains the
  recorded tensor construction. Scalar extension is the existing
  `SheafOfModules.changeOfRings`, not a second tensor construction.
* `Sheaf.Paper.ContinuousConstructibleModule`: `continuousModulePullback`,
  `continuousCoefficientInverseImageMap`, and `IsContinuousConstructible` were
  read in full. Its public imports supply `latticeModuleRing`,
  `integralLatticeCoefficientMap`, and `latticeCoefficientIntegers`.
* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the canonical
  `U.ι` supplies the open immersion rather than adding a second predicate.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage` and `Scheme.proEtaleModuleInverseImage`,
  used by the canonical `continuousModulePullback` definition. Their signatures
  and docstrings were checked, including their independent site universes.

The stated proof dependencies are imported privately, including the existing
etale-local lattice, finite-etale descent, stratification, reduced-source
factorization, object inverse-image restriction, localization, and tensor
comparison modules. No implementation of those results is copied.

Edge cases checked before drafting: the empty scheme is explicitly excluded by
`Nonempty X`; zero and varying ranks are included by finite local freeness; X may
be reducible or disconnected (no integral or connected hypothesis was introduced).
The extracted open need only be nonempty, not dense in every component. The bound
may be zero, and ramified finite extensions are allowed. There is no special
residue characteristic assumption beyond the stated invertibility of l on X.

Searches for existing statements (all through prescribed tools):

* LeanFinder via msearch.py: "A lisse sheaf over a finite extension of Q_l on a
  nonempty reduced noetherian scheme admits a finite locally free integral lattice
  on a nonempty quasi compact open subscheme". Eight hits on finite-type local
  generators, integral schemes and integral closure; none is this theorem.
* Loogle via msearch.py: `"SheafOfModules", "IsFiniteLocallyFree"`. Zero hits.
* Mathlib grep via msearch.py, AlgebraicGeometry:
  `lisse|integral.?lattice|constructible.*module`. Zero hits.
* LeanSearch via msearch.py: "A lisse p-adic sheaf admits an integral lattice on a
  nonempty open subscheme". Eight hits on integral schemes and PadicInt, no match.
* rg of both project roots `lean/WeilConjectures` and `lean/Sheaf`:
  `lem-weil-pbc-lisse-lattice-reduced-open|exists.*lattice.*open|lattice.*reduced`.
  No existing matching declaration. Concept searches for lisse/lattice found the
  existing coefficient, lattice-pair, etale-local and finite-etale descent APIs
  used here. Checked the full finite-local-free definition in the upstream module;
  it permits varying and zero ranks. The node itself is new and has no repair note.

Validation: prescribed scompile.py compiled the delivered file in sandbox and
library modes, with no errors or warnings. No local or global build was run.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
