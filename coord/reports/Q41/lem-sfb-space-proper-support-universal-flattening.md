## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperSupportUniversalFlattening` states
`AlgebraicGeometry.AlgebraicSpace.exists_universalFlattening_of_properSupport`.
Its only theorem has proof `sorry`. There are no new definitions, new nodes,
dependency repairs, or statement corrections. The source was read in
`literature/stacks-project/spaces-flat.tex`: lemma-proper-pure (0CVI),
lemma-when-universal-flattening (0CX2), and the schemehood paragraph of
theorem-existence (0CXB). These agree with the supplied statement and proof.

Hypotheses and conclusions, clause by clause:

- The ambient base Spec Z is `Spec (.of (ULift.{u} ℤ))`, the universe-polymorphic
  spectrum of the integers. `specULiftZIsTerminal.from (Spec R)` gives the unique
  structural map of Spec R to that base. `R : CommRingCat.{u}` ranges over arbitrary
  commutative rings in the chosen scheme universe, including the zero ring.
- The algebraic space is `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`, and its
  structural map to Spec R is `f : X ⟶ schemeSpace (Over.mk (... (Spec R)))`.
- Separatedness is exactly `hsep : MapIsSeparated f`.
- Finite presentation is `hfp : ProperQuotFinitePresentation f`, whose definition
  is chartwise local finite presentation, quasi-compactness, and quasi-compact
  diagonal. In particular this does not replace finite presentation by finite type.
- `F : X.QCoh` supplies the existing quasi-coherence predicate, and
  `hF : F.obj.IsFinitePresentation` is Mathlib's local finite free presentation
  predicate. Its generators and relations are both finite.
- `hsupp` is exactly the stated carrier condition: an algebraic space Z and a map
  i into X, `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`,
  `MapIsProper (i ≫ f)`, and a module G with `G.IsQuasicoherent`, `G.IsFiniteType`,
  and `Nonempty ((moduleDirectImage i).obj G ≅ F.obj)`. It does not assume the
  carrier is finitely presented or that X itself is proper.
- The representing scheme and map are `∃ (T : Scheme.{u}) (h : T ⟶ Spec R)`.
- The finite-presentation conclusion is `LocallyOfFinitePresentation h ∧
  QuasiCompact h ∧ QuasiSeparated h`, including the quasi-separated clause the
  node expressly requires.
- The monomorphism is rendered with the node's explicit definition:
  `∀ B : Scheme.{u}, Function.Injective (fun g : B ⟶ T ↦ g ≫ h)`.
  Thus this quantifies over all scheme tests, not only affine or field tests.
- An arbitrary R-scheme is `B : ProperQuotTest (schemeSpace (Over.mk (...)))`.
  Its underlying scheme is `B.left.left`; its structural map to Spec R is
  `(yoneda.preimage B.hom).left`. Yoneda is fully faithful, so these tests are
  precisely schemes with their specified maps to Spec R. The map to Spec Z is
  unique; its presence in the over-category imposes no additional restriction.
- `properQuotFibre f B` is the actual sheaf fibre product X times_R B. The module
  in the conclusion is the existing tensor pullback
  `(moduleTensorPullback (properQuotFst f B)).obj F.obj`, not an arbitrary module.
- On every `U : (properQuotFibre f B).EtaleSite`, restriction is
  `(schemeRestriction (properQuotFibre f B) U).obj (...)`. Its `IsFlatOver` map is
  exactly the scheme map of the chart followed by `properQuotSnd f B`. The
  recorded affine-local scheme flatness predicate is equivalent to the stated
  stalkwise condition for these quasi-coherent modules.
- The final biconditional says that this flatness holds exactly when there exists
  a unique `g : B.left.left ⟶ T` with
  `g ≫ h = (yoneda.preimage B.hom).left`. Combined with the preceding injectivity
  clause, `∃!` is exactly the node's existence biconditional plus uniqueness,
  without strengthening the assertion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  and `AlgebraicGeometry.Spec` (for def-pc-scheme and def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `EtaleSite`, `Modules`, and their small-etale structure.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, used by the existing proper Quot fibre.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, the full
  subcategory for `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`
  and `moduleTensorPullback`, specified by the recorded universal properties.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, read at its full affine-local definition.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotFinitePresentation`,
  `ProperQuotTest`, `properQuotFibre`, `properQuotFst`, and `properQuotSnd`.
  The carrier and chartwise-flatness formulas are those of `ProperQuotient`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`
  and `MapIsProper`, with their chartwise and topological definitions.
- The size convention is rendered by the explicit universe u. Scheme test objects
  and rings use that same universe, so no smaller independent universe makes the
  quantification vacuous. Modules retain the universe supplied by X.Modules.

Statement dependencies are exposed through the public import of the proper Quot
module. Additional public Mathlib imports supply the terminal integer spectrum
and scheme finite-presentation predicates. The recorded proof dependencies
`def-kun-transcendence-degree` and `lem-a1-separated-locally-qf-space-representable`
have plain imports. The other three proof-only theorem nodes have no recorded
Lean declarations and are not imported; the proof docstring retains all their
roles and the complete five-step proof from this node. No proof-only prerequisite
is needed to type the statement.

Searches (2026-10-24):

- msearch LeanFinder: "Universal flattening scheme representing flat base changes
  of a finitely presented module with proper support". Eight hits about flat
  scheme morphisms, their base changes, and coproducts; none represents this locus.
- msearch LeanSearch: "Universal flattening of finitely presented quasi coherent
  module with proper support". Eight hits on flat modules and finite-presentation
  data; no universal flattening theorem.
- msearch Loogle: `"flattening"`. One unrelated BVDecide configuration field.
- msearch grep in Mathlib/AlgebraicGeometry:
  `flattening|universal.*flatten|properSupport`. Zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for
  `universal.*[Ff]latten|flattening|properSupport.*[Ff]lat|exists.*[Ff]latten`:
  unrelated tensor reassociations, admissible-blowup flattening, and affine
  dimension-filtered flattening. None states this scheme representing property.
- rg for the item id in lean/WeilConjectures: no hits. Exact proposed declaration
  names were searched in Mathlib, WeilConjectures and Sheaf: no existing declaration.
- Targeted source searches for the supporting notions found the existing proper
  Quot interface, so no duplicate predicate or fibre-product construction is added.

Edge cases checked mathematically before drafting: F = 0 permits T = Spec R,
including X empty. A module already flat over R also permits the identity
flattening. The zero ring and empty scheme tests are allowed. No reducedness,
Noetherian hypothesis, nonemptiness or flatness of X is imposed. For R = k[t]
and F = R/(t) on Spec R, the expected representing scheme is D(t) disjoint union
Spec k: it is a monomorphism of finite presentation, although it need not be an
open immersion or a closed immersion. The conclusion allows exactly this case.
All tests include non-affine schemes and nilpotent thickenings.

Validation: prescribed scompile.py compiled the file both in sandbox mode and
under its library module name, with no errors or unexpected warnings (1.7 s and
1.6 s). No global build or direct repository mutation was performed.

## Second reading by Q41

(Written by the independent maintainer second reader; the delivered section was a
self-check by the authoring worker and is replaced by this reading.)

Node statement as a list, with the Lean that renders it and the verdict:

1. Base Spec Z, universes of the size convention: `Spec (.of (ULift.{u} ℤ))`,
   one universe u for R, schemes and tests. Correct.
2. R any commutative ring: `R : CommRingCat.{u}` (zero ring included). Correct.
3. Algebraic space X with X → Spec R: `X : AlgebraicSpace (Spec ℤ)`,
   `f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec R)))`. Correct.
4. f separated: `MapIsSeparated f` (diagonal representable by closed immersions,
   def-sfb-space-morphism-properties). Correct.
5. f of finite presentation (qc, qs = qc diagonal, chartwise lfp):
   `ProperQuotFinitePresentation f`, the def-sfb-space-proper-quot-functor
   predicate with exactly these three clauses. Correct, not weakened to finite type.
6. F finitely presented quasi-coherent: `F : X.QCoh`, `F.obj.IsFinitePresentation`
   (Mathlib local finite free presentation). Correct.
7. Proper support: closed immersion i : Z → X (representable by closed
   immersions), Z proper over Spec R (`MapIsProper (i ≫ f)`), G quasi-coherent of
   finite type with `i_*G ≅ F`. Verbatim the `properSupport` carrier of the landed
   `ProperQuotient`, with the fibre replaced by X. Correct; G is not required to be
   finitely presented and X is not required proper.
8. Scheme T and h : T → Spec R of finite presentation:
   `LocallyOfFinitePresentation h ∧ QuasiCompact h ∧ QuasiSeparated h`. Correct.
9. Monomorphism in the node's explicit sense (injective on Hom(B, -) for every
   scheme B): `∀ B : Scheme.{u}, Function.Injective (· ≫ h)`. Correct.
10. Every R-scheme B: `B : ProperQuotTest (schemeSpace …)` = CostructuredArrow
    yoneda; structural map `(yoneda.preimage B.hom).left`. Yoneda is fully faithful
    and the map to Spec Z is unique, so these are exactly R-schemes. Correct.
11. F_B on X ×_R B flat over B: `moduleTensorPullback (properQuotFst f B)` on the
    sheaf fibre product `properQuotFibre f B`, restricted to every étale scheme chart
    and tested with `Scheme.Modules.IsFlatOver` along chart → B — the same rendering
    as `ProperQuotient.flat` of the landed proper-quot node. For quasi-coherent
    modules affine-local flatness is stalkwise flatness (def-pc-scheme-module-flat-over).
    Correct.
12. Factorization iff flat, and uniqueness: `(∃! g, g ≫ h = str) ↔ flat`. With the
    separate injectivity clause, ∃! ⇔ ∃, so this is exactly existence-iff-flat plus
    uniqueness; not strengthened. Correct.

Edge cases: F = 0 or F flat (T = Spec R); X empty; R = 0; empty and non-affine
tests, nilpotent thickenings; R = k[t], F = R/(t) gives T = D(t) ⊔ Spec k, a
finite-presentation monomorphism neither open nor closed, which the conclusion
allows. No Noetherian, reducedness or flatness assumption is added.

Source: spaces-flat.tex 0CVI (proper support ⇒ universally pure), 0CX2(1)
(universal flattening exists, f.p. monomorphism), 0CXB schemehood via
spaces-morphisms 0463 + 03XX. The node's separatedness hypothesis is the source's.

One definition per notion: no existing universal-flattening declaration in Mathlib,
lean/Sheaf or lean/WeilConjectures; every notion uses the recorded owners
(proper-quot interface, morphism properties, QCoh, tensor pullback, IsFlatOver).
The item is not landed by another group (live record has no `lean`).

Records: `lean.statement` is verbatim the file signature; no new nodes, no
dependency module changes, no statement change; proof is `sorry`; module and
theorem docstrings carry source places, `(blueprint: …)` and the five proof steps.
No mismatch found; nothing in the Lean changed.
