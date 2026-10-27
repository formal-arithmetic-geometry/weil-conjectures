# SheafOfModules.ClopenComparisonTensorSquare interfaces

## Reason

The proof needs independently stated construction and coherence lemmas using the item's
record types. Move those types and the definitions to a shared module to avoid an import
cycle, and publicly re-export them from the original module. Every name, universe,
binder, field, visibility and definition body remains unchanged.

## Old

In lean/Sheaf/SixFunctors/ClopenComparisonTensorSquare.lean:

```lean
/-- The Cartesian open square inside the proper/open square. The ring map is
written in its adjoint direct-image form, exactly as in `Input`.
Source: Stacks 0F7B, 03D7 (blueprint: lem-sf-clopen-comparison-tensor-square). -/
def input (m : Mode) {B C D : Scheme.{u}} (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion i] (R : Sheaf (topology m D) CommRingCat.{u + 1})
    (S : Sheaf (topology m B) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m D) (topology m B)).obj S) : Input m where
  U := C
  U' := CategoryTheory.Limits.pullback p i
  X := D
  X' := B
  gU := pullback.snd p i
  j' := pullback.fst p i
  j := i
  g := p
  square :=
    { w := pullback.condition.symm
      isoPullback := pullbackSymmetry p i
      hom_fst := pullbackSymmetry_hom_comp_fst p i
      hom_snd := pullbackSymmetry_hom_comp_snd p i
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  R := R
  S := S
  coefficient := c

/-- A presentation of the canonical 07A4 comparison for a possibly nonexact
ringed pullback. Its ordinary unit formula fixes pure tensors. The representative
square uses the published signed ProjectionRestriction.total map and the actual left-derived counit;
it does not assume the ordinary pullback exact.
Source: Stacks 03EL, 07A4 (blueprint: lem-sf-clopen-comparison-tensor-square). -/
structure PullTensor (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology m Y) CommRingCat.{u + 1})
    (S : Sheaf (topology m X) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S)
    (p : Pullback R S (direct m f R S c)) (a : TensorModel R) (b : TensorModel S) where
  ordinary : ∀ M N : ProjectionRestriction.Mod R,
    p.ordinary.obj (((ProjectionRestriction.tensor R).obj M).obj N) ≅
    ((ProjectionRestriction.tensor S).obj (p.ordinary.obj M)).obj (p.ordinary.obj N)
  pure_unit : ∀ (M N : ProjectionRestriction.Mod R) (W : (Site m Y)ᵒᵖ)
      (x : M.val.obj W) (y : N.val.obj W),
    ((direct m f R S c).map (ordinary M N).hom).val.app W
        ((p.adjunction.unit.app (((ProjectionRestriction.tensor R).obj M).obj N)).val.app W
          (ProjectionRestriction.pure R M N W x y)) =
      ProjectionRestriction.pure S (p.ordinary.obj M) (p.ordinary.obj N) ((baseChange m f).op.obj W)
        ((p.adjunction.unit.app M).val.app W x)
        ((p.adjunction.unit.app N).val.app W y)
  preserves : ∀ P, ProjectionRestriction.resolving R P →
    ProjectionRestriction.resolving S ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  comparison : a.functor ⋙ p.derived ≅ (p.derived.prod p.derived) ⋙ b.functor
  comm : ∀ (P Q : CochainComplex (ProjectionRestriction.Mod R) ℤ) (n l : ℤ),
    ProjectionRestriction.totalComponent a b p.ordinary ordinary P Q n ≫
        p.ordinary.map (((ProjectionRestriction.total R).obj (P, Q)).d n l) =
      ((ProjectionRestriction.total S).obj ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
        (p.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)).d n l ≫
          ProjectionRestriction.totalComponent a b p.ordinary ordinary P Q l
  representative : ∀ (P Q : CochainComplex (ProjectionRestriction.Mod R) ℤ)
      (hp : ProjectionRestriction.resolving R P) (hq : ProjectionRestriction.resolving R Q),
    p.derived.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        b.functor.map (Prod.mkHom
          (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P)
          (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon Q)) ≫
        b.representative.inv.app
          (⟨(p.ordinary.mapHomologicalComplex (.up ℤ)).obj P, preserves P hp⟩,
            ⟨(p.ordinary.mapHomologicalComplex (.up ℤ)).obj Q, preserves Q hq⟩) ≫
        DerivedCategory.Q.map (ProjectionRestriction.totalMap a b p.ordinary ordinary comm P Q) =
      derivedPullbackComplexComparison p.ordinary p.derived p.epsilon
        ((ProjectionRestriction.total R).obj (P, Q))

/-- The remaining open tensor data, with the extension fixed in advance.
The ordinary comparison retains the literal restriction of ProjectionRestriction.pure sections;
`TensorComparison` pins its derived map on all flat K-flat representatives.
The inverse transpose is precisely the open-unit normalization.
Source: Stacks 0GL1, 07A4 (blueprint: lem-sf-clopen-comparison-tensor-square). -/
structure OpenTensor (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1})
    (e : OpenExtension m j R) (a : TensorModel R)
    (b : TensorModel (restrictRing m j R)) where
  ordinary : ∀ M N : ProjectionRestriction.Mod R,
    (OpenTensorNormalization.restrict m j R).obj (((ProjectionRestriction.tensor R).obj M).obj N) ≅
      ((ProjectionRestriction.tensor (restrictRing m j R)).obj
        ((OpenTensorNormalization.restrict m j R).obj M)).obj
        ((OpenTensorNormalization.restrict m j R).obj N)
  pure_sections : ∀ (M N : ProjectionRestriction.Mod R) (W : (Site m U)ᵒᵖ)
      (x : M.val.obj ((openInclusion m j).op.obj W))
      (y : N.val.obj ((openInclusion m j).op.obj W)),
    (ordinary M N).hom.val.app W
        (ProjectionRestriction.pure R M N ((openInclusion m j).op.obj W) x y) =
      ProjectionRestriction.pure (restrictRing m j R)
        ((OpenTensorNormalization.restrict m j R).obj M)
        ((OpenTensorNormalization.restrict m j R).obj N) W x y
  tensorComparison : TensorComparison (OpenTensorNormalization.restrict m j R)
    (restrictionModel j R) a b ordinary
  delta : e.ordinary.mapDerivedCategory.prod (𝟭 _) ⋙ a.functor ≅
    (𝟭 _).prod (OpenTensorNormalization.restrict m j R).mapDerivedCategory ⋙ b.functor ⋙
      e.ordinary.mapDerivedCategory
  inverse_transpose : ∀ M N,
    (exactDerivedAdjunction e.adjunction).homEquiv _ _ (delta.inv.app (M, N)) =
      b.functor.map (Prod.mkHom ((exactDerivedAdjunction e.adjunction).unit.app M) (𝟙 _)) ≫
        tensorComparison.comparison.inv.app (e.ordinary.mapDerivedCategory.obj M, N)

/-- Simultaneous canonical data needed by the three squares. This is a conclusion
of the theorem, not an extra hypothesis on rings or derived objects. The reverse
clopen adjunction has the inverse open unit as its counit; hence its localized unit
is exactly the first-factor projection `(1,0)`. The composite-open tensor map has
its own prescribed transpose, independently of the composite-open equality below.
Source: Stacks 04TS, 0GL1 (blueprint: lem-sf-clopen-comparison-tensor-square). -/
structure Data {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) {A : Scheme.{u}} (s : A ⟶ d.U') [IsOpenImmersion s] where
  tensorP : PullTensor m d.g d.R d.S d.coefficient o.gPull o.tensorX o.tensorX'
  tensorQ : PullTensor m d.gU (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
    (cornerCoefficient t) o.gUPull o.tensorU o.tensorU'
  tensorB : OpenTensor m d.j' d.S o.opens.extension' o.tensorX' o.tensorU'
  extensionS : OpenExtension m s (restrictRing m d.j' d.S)
  tensorA : TensorModel (restrictRing m s (restrictRing m d.j' d.S))
  tensorS : OpenTensor m s (restrictRing m d.j' d.S) extensionS o.tensorU' tensorA
  rightAdjunction : restrict m s (restrictRing m d.j' d.S) ⊣ extensionS.ordinary
  counit_normalization : ∀ M,
    extensionS.adjunction.unit.app M ≫ rightAdjunction.counit.app M = 𝟙 M
  deltaK : (extensionS.ordinary.mapDerivedCategory ⋙ o.opens.jShriek').prod (𝟭 _) ⋙
      o.tensorX'.functor ≅
    (𝟭 _).prod (o.opens.jStar' ⋙
      (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory) ⋙
        tensorA.functor ⋙ (extensionS.ordinary.mapDerivedCategory ⋙ o.opens.jShriek')
  inverse_transposeK : ∀ M N,
    ((exactDerivedAdjunction extensionS.adjunction).comp o.opens.adj').homEquiv _ _
        (deltaK.inv.app (M, N)) =
      tensorA.functor.map
          (Prod.mkHom
            (((exactDerivedAdjunction extensionS.adjunction).comp o.opens.adj').unit.app M)
            (𝟙 _)) ≫
        tensorS.tensorComparison.comparison.inv.app
          (o.opens.jStar'.obj (o.opens.jShriek'.obj
            (extensionS.ordinary.mapDerivedCategory.obj M)), o.opens.jStar'.obj N) ≫
        (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
          (tensorB.tensorComparison.comparison.inv.app
            (o.opens.jShriek'.obj (extensionS.ordinary.mapDerivedCategory.obj M), N))

/-- The actual localized clopen projection, given by the exact reverse adjunction.
Source: Stacks 04TS (blueprint: lem-sf-clopen-comparison-tensor-square). -/
def Data.rho {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) : 𝟭 (ProjectionRestriction.Der (restrictRing m d.j' d.S)) ⟶
      (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory ⋙
        v.extensionS.ordinary.mapDerivedCategory :=
  (exactDerivedAdjunction v.rightAdjunction).unit

/-- The comparison is beta followed by the first-factor projection, with `k_!`
presented by the composite open extension and `P_r` by the composite pullback.
Source: Stacks 0F7B (blueprint: lem-sf-clopen-comparison-tensor-square). -/
def alpha {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (H : ProjectionRestriction.Der (restrictRing m d.j d.R)) :
    o.gPull.derived.obj (o.opens.jShriek.obj H) ⟶
      o.opens.jShriek'.obj (v.extensionS.ordinary.mapDerivedCategory.obj
        ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj
          (o.gUPull.derived.obj H))) :=
  a.beta.hom.app H ≫ o.opens.jShriek'.map (v.rho.app (o.gUPull.derived.obj H))

/-- The three tensor identities and the composite-open normalization, as equalities
of morphisms on the whole ringed-site derived category, naturally in all inputs.
The theta factors write out `P_q P_i = P_b P_p`; no equality after evaluation is used.
Source: Stacks 07A4, 0GL1 and the node's tensor refinement
(blueprint: lem-sf-clopen-comparison-tensor-square). -/
def Equations {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s) : Prop :=
  (∀ (H : ProjectionRestriction.Der (restrictRing m d.j d.R)) (N : ProjectionRestriction.Der d.R),
    o.gPull.derived.map (a.gamma.hom.app (H, N)) ≫
        a.beta.hom.app (o.tensorU.functor.obj (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (o.tensorU'.functor.map
          (Prod.mkHom (𝟙 _) (o.theta.inv.app N))) =
      v.tensorP.comparison.hom.app (o.opens.jShriek.obj H, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (a.beta.hom.app H) (𝟙 _)) ≫
        v.tensorB.delta.hom.app (o.gUPull.derived.obj H, o.gPull.derived.obj N)) ∧
  (∀ (F V : ProjectionRestriction.Der (restrictRing m d.j' d.S)),
    v.rho.app (o.tensorU'.functor.obj (F, V)) ≫
        v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorS.tensorComparison.comparison.hom.app (F, V)) =
      o.tensorU'.functor.map (Prod.mkHom (v.rho.app F) (𝟙 V)) ≫
        v.tensorS.delta.hom.app
          ((OpenTensorNormalization.restrict m s
            (restrictRing m d.j' d.S)).mapDerivedCategory.obj F, V)) ∧
  (∀ (M : ProjectionRestriction.Der (restrictRing m s (restrictRing m d.j' d.S)))
      (N : ProjectionRestriction.Der d.S),
    v.tensorB.delta.hom.app (v.extensionS.ordinary.mapDerivedCategory.obj M, N) ≫
        o.opens.jShriek'.map (v.tensorS.delta.hom.app (M, o.opens.jStar'.obj N)) =
      v.deltaK.hom.app (M, N)) ∧
  (∀ (H : ProjectionRestriction.Der (restrictRing m d.j d.R)) (N : ProjectionRestriction.Der d.R),
    o.gPull.derived.map (a.gamma.hom.app (H, N)) ≫
        alpha a v (o.tensorU.functor.obj (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (v.extensionS.ordinary.mapDerivedCategory.map
          ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
            (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N)) ≫
          v.tensorS.tensorComparison.comparison.hom.app
            (o.gUPull.derived.obj H, o.gUPull.derived.obj (o.opens.jStar.obj N)))) =
      v.tensorP.comparison.hom.app (o.opens.jShriek.obj H, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (alpha a v H) (𝟙 _)) ≫
        v.deltaK.hom.app
          ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj
            (o.gUPull.derived.obj H), o.gPull.derived.obj N) ≫
        o.opens.jShriek'.map (v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorA.functor.map (Prod.mkHom (𝟙 _)
            ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
              (o.theta.hom.app N))))))

```

## New

The exact block above, with only blueprint references updated to its new owner node,
is in lean/Sheaf/SixFunctors/ClopenComparisonTensorSquareData.lean. The original module
has `public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData`.

A text comparison after normalizing blueprint references confirms equality of the
complete declaration block. The target theorem statement stays verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ClopenComparisonTensorSquare | D6 | Public re-export and proof from separate component results. |

`tools/downstream.py Sheaf.SixFunctors.ClopenComparisonTensorSquare --uses
SheafOfModules.ClopenComparisonTensorSquare.Data` reports zero downstream modules and
only the item itself as a declaration user. A source-wide name search likewise finds
no other consumers. No target definition changes meaning.

## Status

landed 20261024T214331-L-589450 2026-10-24 (merge of deliver/D6/Sheaf.SixFunctors.ClopenComparisonTensorSquare)
