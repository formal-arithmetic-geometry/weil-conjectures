## Worker report

The module `Sheaf.CategoryTheory.LocalizedBasisCoefficients` states
`CategoryTheory.Mod.sheaf_localizedBasisCoefficients`, with proof `sorry`.
`CategoryTheory.Mod.LocalizedBasisCoefficients` is a fully written Prop-valued helper
spelling out this node's assertion, rather than a new independent mathematical notion.
The theorem asserts that predicate only for abelian sheaves with the canonical
`sfbSheafTensorStructure`. It does not assert a localization theorem in an arbitrary
monoidal category. No node statement or dependency list was changed.

Sources read: Stacks `sites-modules.tex`, Tags 0EMC `lemma-simple-invert` and 0EMD
`lemma-simple-invert-module` (localizing-sheaves sections, lines 8615–8710), including
the presheaf restriction rule and both universal properties; and
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-prop-sfb-cartesian-coefficients/sk-prop-sfb-cartesian-coefficients-finite-free.proof.md`,
especially lines 10–15, where inverting ell preserves the basis and the coefficient square.
The module's theorem docstring carries all eight proof steps of the node, including
local denominators, killing powers, gluing and standard-generator uniqueness.

Hypothesis and conclusion correspondence:

- The small site is `{C : Type uC} [Category.{vC} C]` with topology `J` and
  `[EssentiallySmall.{w} C]`, the existing tensor dependency's size convention.
  The category in the theorem is exactly `Sheaf J Ab.{w}`, with the monoidal and
  braided structures explicitly taken from `sfbSheafTensorStructure`. The abelian
  structure is the existing `sheafIsAbelian`. Site and coefficient universes remain
  independent subject to the recorded essentially-small convention.
- The ring objects `R T A B` have `[MonObj]` and `[IsCommMonObj]`. The maps `φ`, `jR`
  and `jT` are morphisms between their `Mon.mk` bundles, so their multiplication
  and unit compatibilities are part of the types, not missing assumptions.
- The global section is `t : 𝟙_ H ⟶ R`; the specified global basis sections are
  `b : I → (𝟙_ H ⟶ T)`. The sheaf tensor unit is the sheafified constant integers,
  so maps from it are precisely global sections of an abelian sheaf. No terminal
  object of the site is assumed.
- The arbitrary finite set is `(I : Type uI) [Fintype I]`, with independent index
  universe. An enumeration is harmless data and imposes no nonemptiness condition.
- The given isomorphism is
  `q : (⨁ fun _ : I ↦ regular R) ≅ (comap φ.hom).obj (regular T)`.
  The following `∀ i` hypothesis says that its i-th summand is
  `φ.hom ≫ (ρ_ T).inv ≫ T ◁ b i ≫ μ[T]`, exactly `r ↦ φ(r)b_i`.
  Biproducitivity makes this equivalent to the node's sum formula on all tuples.
- Invertibility of `jR(t)` is
  `IsIso ((λ_ A).inv ≫ (t ≫ jR.hom) ▷ A ≫ μ[A])`.
  This is equivalent to invertibility of that global section: an inverse section
  yields the inverse multiplication map, and the inverse multiplication map
  applied to the unit yields an inverse section. The same clause for `B` uses
  `t ≫ φ.hom ≫ jT.hom`. Both descriptions include the zero ring.
- Each localization universal property quantifies over every commutative ring
  object `D` in the same sheaf category and every bundled ring morphism `f` making
  the specified section invertible, and asserts `∃! g, jR ≫ g = f` (respectively
  `∃! g, jT ≫ g = f`). It does not assert the stronger and generally false claim
  that every section ring is an ordinary localization.
- The conclusion `∃ ψ`, its equation `jR ≫ ψ = φ ≫ jT`, and the following
  `∀ ψ' ... → ψ' = ψ` are exactly existence and uniqueness of the scalar map.
- `qt : (⨁ fun _ : I ↦ regular A) ≅ (comap ψ.hom).obj (regular B)` is the
  A-module isomorphism for that very scalar map. Its i-th summand is explicitly
  `ψ.hom ≫ (ρ_ B).inv ≫ B ◁ (b i ≫ jT.hom) ≫ μ[B]`, giving the node's localized
  finite-sum formula, not merely existence of an arbitrary basis.
- The componentwise map `jR^I` is written, without a new definition, as
  `∑ i, (biproduct.π ... i).hom ≫ jR.hom ≫ (biproduct.ι ... i).hom`.
  Its composite with `qt.hom.hom` equals `q.hom.hom ≫ jT.hom`, the full canonical
  square. The last clause quantifies over all A-linear `f` between the same module
  objects and states that this square implies `f = qt.hom`.
- No injectivity of `φ`, nonzero-divisor assumption on `t`, enough-points condition,
  nonzero ring, or global denominator assumption occurs.

Dependency declarations used and read:

- `Sheaf.CategoryTheory.SheafTensor`: `CategoryTheory.sfbSheafTensor_properties`,
  `sfbSheafTensor_monoidalPreadditive`, `sfbSheafTensor_hasWeakSheafify`, and the
  imported `sfbSheafTensorStructure` from `SheafTensorStructure`. The theorem
  supplies the sheaf tensor, its symmetric structure, and abelian size infrastructure.
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`: the recorded
  `CategoryTheory.Functor.monObjCompForget₂` and surrounding docstring were read.
  The initial general part of that node uses existing `MonObj`, `Mon`,
  `IsMonHom`, and `IsCommMonObj`; those are the objects used here. The upstream
  `RingObjects.Ab` source confirms the tensor of Ab is over the integers.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, module
  morphisms and `Mod.regular`. The source was read through the action axioms and
  regular-module construction. `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`
  supplies the finite biproducts of these same internal modules.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.comap`, as
  recorded by the change-of-scalars node. Its docstring and `comap_obj_smul` confirm
  that the restricted action is `φ ▷ N.X ≫ γ` and the underlying object is unchanged.
- Stated proof dependencies are imported non-publicly:
  `Mathlib.CategoryTheory.Sites.PreservesSheafification` for the recorded
  `sheafifyComposeIso`/`sheafComposeIso_hom_fac`/`PreservesSheafification` match, and
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` for
  `CategoryTheory.sheafification_sections_local`.
  `lem-sfb-ring-localization-sheafification` has no Lean record yet and hence no
  import; it is a proof dependency, not a missing object in this statement.

Edge cases checked mathematically: empty I makes both finite sums empty and the
source module zero; q then forces T zero and the localized conclusion remains zero.
For t = 0 or nilpotent t (e.g. Z/4 with t = 2), both localizations are zero objects;
multiplication on the zero object is an isomorphism, so no case is excluded. For
unit t the localizations are isomorphic to the original rings. Noninjective φ is
allowed (in particular the zero-ring and empty-basis cases). An empty site is
allowed, as are arbitrary sites without a final object. A nontrivial site may
require different denominators on covering members; no sectionwise localization
hypothesis appears. All finite index universes are explicit and independent.
No statement fault or dispute was found.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
with group N0 and this item:

- LeanFinder: `A finite basis of an internal algebra in abelian sheaves remains a
  basis after localization at a global scalar` returned ordinary module results,
  chiefly `Module.Basis.localizationLocalization` and `Module.Basis.ofIsLocalizedModule`.
- Loogle: `IsLocalizedModule, Module.Basis` returned those same ordinary-module
  constructions and their application/representation lemmas.
- grep: `ofIsLocalizedModule|localizationLocalization`, restricted to
  `RingTheory/Localization`, returned the ordinary-ring declarations.
- LeanSearch: `Localizing a finite basis of an internal ring sheaf preserves the
  specified basis and canonical scalar map` returned those ordinary-module
  constructions, not an internal sheaf theorem.
- Read `Mathlib/RingTheory/Localization/Module.lean` lines 95–185: these require
  ordinary scalar ring localizations and localized modules; they do not express
  localization of ring objects in sheaves with the given scalar map and square.
- Direct rg searched `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, localization/basis patterns,
  `LocalizedBasisCoefficients` and `localizedBasisCoefficients`. No exact theorem
  or conflicting declaration was found. Existing finite-coordinate and monoidal
  finite-free-transport modules were read; neither states localization.

Validation: prescribed scompile.py compiled this file both as sandbox and as its
library module, with no errors or warnings (11.6 s and 10.7 s respectively).

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
