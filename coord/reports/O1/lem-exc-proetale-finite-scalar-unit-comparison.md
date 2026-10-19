## Worker report

States `AlgebraicGeometry.ProEtale.finiteScalarUnitComparison` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison`. Its only theorem has
proof `sorry`. All five helper definitions have actual data. They belong to the
coefficient-comparison notion of this node and are listed in `lean.declarations`.
No independent definition node, dependency replacement, or natural-statement
correction is needed.

The previous worker mistook the merged stage-1 split for a stage-2 completion.
The current base node has a reviewed three-step natural-language proof and no
`lean` record. The NO report explicitly describes its stage-1 splitting work;
it supplies no Lean declaration and is not a reason to split the node again.
This delivery supplies only the missing stage-2 statement.

### Hypotheses and every clause

| Natural statement | Lean rendering |
| --- | --- |
| Arbitrary morphism of schemes f:X→Y | `{X Y : Scheme.{u}} (f : X ⟶ Y)`; no geometric property instances. |
| Two finite rings, possibly noncommutative | `{R S : Type (u+1)}`, `[Ring R] [Finite R]` and `[Ring S] [Finite S]`; no `CommRing`. |
| Discrete coefficient topology | `[TopologicalSpace R] [DiscreteTopology R]` and the same for S, matching the coefficient dependency exactly. |
| Unital ring homomorphism φ:R→S | `(φ : R →+* S)`. |
| Compatible small pro-etale sites | The recorded `Scheme.ProEt.topology` and `Scheme.proEtaleSiteModel`, with base change `Scheme.proEtaleBaseChange f`; objects remain in u+1 and original morphisms in u. No universe equality or restricted class of schemes is assumed. |
| Coefficient sheaves and left module sheaves | The recorded `finiteCoefficientRingSheaf T C` and `FiniteCoefficientModules T C`, using Mathlib `SheafOfModules`. |
| φ_T is pointwise composition followed by sheafification | `finiteScalarPresheafMap φ T` maps a continuous function s to φ∘s and `finiteScalarRingMap φ T` applies `presheafToSheaf.map`. |
| P_T is restriction of scalars | `finiteScalarRestriction φ T` is exactly `SheafOfModules.restrictScalars (finiteScalarRingMap φ T)`. |
| f_C^* uses inverse image and c_f inverse | The existing `finiteCoefficientModulePullback f C` from `ProEtaleConstantExact`, without any replacement construction. |
| f_{C,*} is sectionwise direct image through rho | `finiteScalarModuleDirectImage f C` is Mathlib `SheafOfModules.pushforward` along the original base-change functor, with the recorded `finiteCoefficientDirectImageMap f C`. This interface works for arbitrary rings; the existing `finiteCoefficientModuleDirectImage` requires commutativity. |
| Module adjunctions are the lifted abelian adjunctions | `adjR` and `adjS` are adjunctions for precisely those functors. The first two conjuncts fix their unit at every section to `finiteScalarModuleUnitSection`, extracted from the actual small-model `pullbackPushforwardAdjunction (finiteCoefficientModelRingUnit f C)`. The next two conjuncts identify the underlying unit with the actual `Scheme.proEtaleSheafAdjunction f AddCommGrpCat` unit via eR/eS. |
| Natural pullback comparison α | Existential `α : finiteCoefficientModulePullback f S ⋙ finiteScalarRestriction φ X ≅ finiteScalarRestriction φ Y ⋙ finiteCoefficientModulePullback f R`. |
| Natural direct-image comparison β | Existential `β : finiteScalarModuleDirectImage f S ⋙ finiteScalarRestriction φ Y ≅ finiteScalarRestriction φ X ⋙ finiteScalarModuleDirectImage f R`. |
| Underlying abelian-sheaf maps are identities | Fifth conjunct: eR applied after α equals eS on every section; eR/eS identify the chosen module pullbacks with the same abelian inverse image. Sixth conjunct: β sends every section m to m. Naturality is part of the natural-isomorphism types. |
| Preserve the specified adjunction unit | Final conjunct is `P_Y.map (adjS.unit.app N) ≫ β.hom.app (f_S^*.obj N) ≫ f_Rstar.map (α.hom.app N) = adjR.unit.app (P_Y.obj N)`, for every N. Lean composition runs left to right, giving exactly the displayed equation of the node. |
| No further assumptions | No flatness, immersion, Noetherian, support, constructibility, characteristic, or nonzero hypotheses occur. |

The existential eR/eS are the identifications needed to express “identity on the
underlying inverse image” for a pullback represented by a small-model left
adjoint. They are not arbitrary supplied comparison maps or extra assumptions:
they are asserted to exist and are fixed by the actual unit. Concretely, their
inverse is the abelian adjunct of the prescribed module unit. The unit also
determines the lifted adjunction with its fixed left and right functors. Thus
none of these witnesses permits replacing the node's functors or units by an
unconstrained map, chosen abstract equivalence, or twisted adjunction.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  the recorded declaration of `def-pc-scheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientPresheaf`,
  `finiteCoefficientRingSheaf`, `FiniteCoefficientModules`, with full signatures
  and source docstrings read; imported through the constant-exact dependency.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the exact `mathlib_match` of
  `def-pc-sheaf-restrict-scalars`; no Lean record is required for that Mathlib leaf.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientModulePullback`, `finiteCoefficientModuleInverseImage`, and
  `finiteCoefficientModelRingUnit`. These are the recorded noncommutative
  transported-action inverse image, including its actual small-model ring unit.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `finiteCoefficientDirectImageMap`, `finiteCoefficientInverseImageMap`, and
  `finiteCoefficientInverseImageMap_isIso`. The actual rho, constructed by
  sheafifying pullback of continuous functions, is used for both direct images.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, the recorded module
  of `def-weil-proetale-inverse-image`, is imported. Its commutative primary
  declaration `sfIntrinsicConstantModuleAdjunction` is not misapplied to the
  noncommutative case. The reexported original `ProEtaleInverseImage` supplies
  `Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`,
  `proEtaleModuleToModel` and `proEtaleSiteModel`. Their signatures and docstrings
  were read directly in that original module.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`, is reexported by the finite-modules
  dependency. `SheafOfModules.toSheaf` and sectionwise linear morphisms are
  exactly the abelian-forgetting interpretation of this node.

All proof dependencies are also statement dependencies and are imported through
these modules. The pro-etale framework note `coord/pefw-upstream-framework.md`
was read. The module-object framework's condensed/commutative coefficient
interfaces do not replace the recorded ordinary noncommutative left modules.

### Source and edge cases

Read Stacks `sites-modules.tex`, Tag 03D3,
`lemma-adjoint-push-pull-modules`, including its proof of the linearity of the
actual unit. Read the node's three proof steps and its recorded coefficient and
inverse-image constructions. The theorem docstring reproduces the proof route:
constant-section equality, open-fibre gluing and sheafification, identity linear
comparisons, and faithfulness for the unit equation.

Checked before writing: φ=id, f=id, empty X and empty Y when a morphism exists,
the zero coefficient ring, and noncommutative finite rings such as M₂(F₂).
The coefficient maps preserve zero and one even when 0=1. Empty-object sections
are sheafified, so no injectivity of constant sections is assumed. No nonempty
or nontrivial condition excludes these cases. The constructions use genuine
small models rather than identifying the site object and morphism universes.
The theorem does not assert the units are isomorphisms.

### Searches

- `msearch.py leanfinder`, query: “Inverse image and direct image of module
  sheaves commute with restriction of scalars along a finite ring homomorphism
  and preserve the adjunction unit”. Eight hits: generic
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_*`,
  `SheafOfModules.PullbackConstruction.adjunction`, pushforward units, and open
  scheme restriction adjunctions. None states this finite noncommutative
  coefficient comparison with the specified unit.
- `msearch.py loogle`, query:
  `SheafOfModules.restrictScalars, SheafOfModules.pullback`: zero hits.
- `msearch.py grep`, query:
  `restrictScalars.*(pullback|pushforward|unit)|pullback.*restrictScalars`, in
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- Direct `rg` in `WeilConjectures/SixFunctors/ProEtale` for this blueprint id,
  scalar unit, and restriction/pullback/pushforward combinations: no exact hit.
- Direct `rg` for the item id in all upstream `WeilConjectures` and side
  `lean/Sheaf`: no hit. Direct `rg` for the proposed six declaration names in
  those trees: no hit.
- Side source search found `ProEtaleFixedScalarRestrictionDirectImage` and
  `FiniteConstantCoefficientTransport`. Read the latter's full constant-scalar
  interfaces and the fixed-scalar declarations: these concern commutative or
  derived fixed-ring presentations, not the ordinary two finite noncommutative
  ring-sheaf functors and their unit. Read the already recorded ordinary
  `ProEtaleFiniteCoefficientDirectImage`: it has `[CommRing Λ]`, so its precise
  noncommutative pushforward specialization is supplied here with the recorded
  arbitrary-ring rho, rather than adding a commutativity hypothesis.

No statement dispute or mathematical correction. No dependency or new-node
module is needed. The main theorem is the only postponed proof and corresponds
to this existing DAG node; construction helpers contain no postponed proofs.

### Validation

`scompile.py N1 lem-exc-proetale-finite-scalar-unit-comparison` compiled the
single delivered file both as a sandbox module (11.4 seconds) and under its
library module name (9.6 seconds), with no errors or warnings. The first draft's
continuity-lemma application and unused extensionality pattern were repaired
before this clean run. The declaration reader finds exactly the five recorded
helper definitions and the one recorded theorem. The file has no line over
100 characters, no auto-implicit variable, and exactly one `sorry`, the entire
proof of the named theorem.

## Second reading by N1

Independent maintainer second reading of immutable delivery
`14f55e082c21a24be819209791994c45bd45ff2d`, 2026-10-17.
This section was supplied by the independent maintainer reader, not by an
additional N1 worker. The delivered section was a placeholder; this replacement
records the actual reading required by H11. The worker report above is retained.

I read the packet, the immutable node, every statement dependency and its record,
the complete delivered module, and the source declarations used by its terms.
The mathematical statement is correct. No Lean or node replacement is needed.

| Hypothesis or conclusion | Independent check and verdict |
| --- | --- |
| Arbitrary schemes and morphism | `Scheme.{u}`, `{X Y}`, and `f : X ⟶ Y` introduce exactly these objects; no property of f is assumed. Pass. |
| Finite unital, possibly noncommutative rings | `R S : Type (u+1)`, `Ring`, `Finite`, and `φ : R →+* S`; no `CommRing` or `Nontrivial`. The discrete topology instances express the coefficient dependency's topology. Pass. |
| Compatible small pro-etale sites | The imported `Scheme.proEtaleBaseChange` is weakly-etale base change with the actual `Scheme.ProEt.topology`. The `AsSmall.{u+1}` model retains all original objects and enlarges Hom only. Pass. |
| Specified coefficient sheaves and left modules | `finiteCoefficientPresheaf` is continuous functions on quotient connected components; `finiteCoefficientRingSheaf` is its ring sheafification; `FiniteCoefficientModules` is the recorded abbreviation for Mathlib `SheafOfModules`. Pass. |
| Pointwise coefficient map | `finiteScalarPresheafMap` sends s to φ∘s, with actual continuity and ring-map fields; `finiteScalarRingMap` sheafifies it. Pass. |
| Restriction P_T | `finiteScalarRestriction` uses the exact Mathlib `SheafOfModules.restrictScalars`; additive sheaves and maps are retained. Pass. |
| Transported pullback f_C^* | Uses the recorded `finiteCoefficientModulePullback`, its model module pullback along the ring adjunction unit, and scalar restriction along the inverse of the canonical c_f. Pass. |
| Sectionwise direct image f_C,* | `finiteScalarModuleDirectImage` specializes Mathlib pushforward to the recorded noncommutative `finiteCoefficientDirectImageMap` rho. No commutative substitute is used. Pass. |
| Specified lifted adjunctions | The first two conjuncts prescribe every section of `adjR.unit` and `adjS.unit` by the actual model adjunction unit in `finiteScalarModuleUnitSection`. The next two conjuncts identify these with the abelian adjunction unit under eR/eS. These witnesses are conclusions, not hypotheses. Pass. |
| Natural pullback isomorphism α | Its functor type is f_S^* then P_X isomorphic to P_Y then f_R^*, in the node's direction. Pass. |
| Natural direct-image isomorphism β | Its functor type is f_S,* then P_Y isomorphic to P_X then f_R,*, in the node's direction. Pass. |
| Identity underlying maps | The fifth conjunct states eR∘α=eS on every section; these are the unit-preserving identifications with abelian inverse image. The sixth states β(m)=m on every section. Natural isomorphisms already include naturality and inverse maps. Pass. |
| Actual-unit compatibility | The last conjunct is P_Y(η_S), followed by β and f_R,*(α), equal to η_R. Lean's left-to-right composition is precisely the node's equation. Pass. |
| No extra assumptions | No flatness, immersion, Noetherian, support, constructibility, characteristic, nonzero or nonempty binder. Pass. |

The auxiliary identifications do not permit an arbitrary replacement of the
canonical unit. For a fixed left and right adjoint a prescribed unit determines
the adjunction; the section equations prescribe that unit completely. The
underlying module inverse image is the abelian inverse image by the ring-unit
pullback universal property (Stacks 03D3). The unit-preserving comparison with
that abelian inverse image is therefore the canonical one. This explains why
existential eR/eS faithfully encode the identity-map clause for the recorded
small-model representation.

Dependencies checked in the read-only group clone: `ProEtaleFiniteModules`
(defining presheaf, ring sheaf, module category); `ProEtaleConstantRingMap`
(rho from fibre-product precomposition and sheafification, c_f as its adjunct,
and its isomorphism theorem); `ProEtaleConstantExact` (model ring unit, module
inverse image, scalar transport); `SfIntrinsicRealizationTransport` and its
reexported `ProEtaleInverseImage` (actual base change, sheaf adjunctions and
model transport); and `RingedSiteModules` (transparent Mathlib category).
The Mathlib `Scheme`, `Scheme.Hom`, `SheafOfModules`, `toSheaf`,
`restrictScalars`, `pushforward`, `pullback` and
`pullbackPushforwardAdjunction` declarations were opened directly. The
commutative primary adjunction in `SfIntrinsicRealizationTransport` is not used
as a noncommutative adjunction.

Source read: Stacks `sites-modules.tex` lines 988–1100, especially Tag 03D3,
`lemma-adjoint-push-pull-modules`, and Tags 03D1/03D2; `proetale.tex` lines
4675–4690, Tag 09A5. The source requires no extra geometric hypothesis for the
site morphism or lifted adjunction. The coefficient refinement is justified by
rho^S φ_Y = f_*(φ_X) rho^R: both maps agree on constants, then on continuous
functions using open fibres, then after sheafification. Adjunction gives the
corresponding c_f square. This proves linearity of the identity comparisons;
forgetful faithfulness gives the displayed unit equation. The module docstring
contains these steps and every helper has a source/blueprint docstring.

Checked edge cases: empty source; empty target whenever f exists; zero ring
and zero modules; φ=id; f=id; noncommutative finite matrix rings; noninjective
and nonflat coefficient maps. Constants need not be injective on an empty
object. The sheafifications and empty-cover axiom handle this. There is no
characteristic restriction. All binders are bound with `autoImplicit false`;
schemes have universe u, original site objects u+1 and Hom u, coefficients and
abelian section groups u+1. The model changes no scheme bound or coefficient
class and does not force site object and Hom universes equal.

Independent searches used LeanFinder for “Sheaves of modules change coefficient
rings inverse image direct image natural isomorphism compatible adjunction
unit”, LeanSearch for “Pullback of ringed sheaf modules commutes with changing
scalars by restriction and preserves the unit of pullback pushforward”, Loogle
for `SheafOfModules.restrictScalars`, and direct rg searches for scalar,
restriction, pullback, pushforward and unit in Mathlib, upstream and side Lean.
The semantic hits are generic pullback adjunctions and unit-module Hom formulas;
Loogle gives restriction and its defining formulas. No exact theorem was found.
Read the side framework's `ModuleObjects/ChangeOfScalarsSquare`: it uses internal
module objects and monoidal comparisons, not these ordinary finite ring sheaves.
The etale `BaseChange/RestrictScalars.restrictScalars_map_unit_app` is on a
different site. `ProEtaleFixedScalarRestrictionDirectImage` is a derived
fixed-scalar comparison. `FiniteConstantCoefficientTransport` has commutative
strict-tower coefficients. The existing ordinary finite direct-image wrapper
requires `CommRing`. The delivery reuses Mathlib's constructions and supplies
only the required noncommutative specialization; no second category or
pro-etale substitute is introduced.

The node's `lean.statement` equals the file signature verbatim, including every
conjunct. Its six recorded declarations are exactly the five data-bearing
helpers and one theorem in the file. There is exactly one sorry, the entire
theorem proof; the proofs within helper structure fields only verify the
constructed ring homomorphism and its naturality. No independent local theorem
was proved. No statement correction, new node, missing prerequisite or dependency
repair is required, so a §1(C) citer audit is inapplicable.

Compiler reproduction: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N1 lem-exc-proetale-finite-scalar-unit-comparison snapshot/lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteScalarUnitComparison.lean`
from the immutable review directory. Exit code 0, no diagnostics; sandbox
`Sheaf/Stage2/Sandbox0.lean` 5.6 s and library
`Sheaf/AlgebraicGeometry/ProEtaleFiniteScalarUnitComparison.lean` 6.4 s.
The installed wrapper currently uses server confirmation with an isolated side
source overlay (`/dev/shm/nt-tmp/nt-local-compile-zybncux5/.lbuild`); it was used
as installed. No direct ssh command, lake/global build, repository edit, live
Lean write, delivery or Git mutation was performed by this review.

Finding and repair: H11, the delivered second-reading section said only that
no second reading had occurred. This complete replacement report supplies the
actual independent review. No mathematical or Lean change was needed.
