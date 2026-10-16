# module_pullback_tensor_iso_tail

## Reason

The returned delivery correctly rejects the original arbitrary-functor tail. The first repair
restored the geometric and module adjunctions but still omitted the operation equations that
specify geometric module inverse image and direct image. That repair is also false.

Take the site with one object and automorphism group C₂, with the trivial topology. Sheaves of
sets are C₂-sets and module sheaves over a constant ring are modules with a commuting involution g.
Set L = V = identity, R = A = Z[t], S = Z and c(t) = 0. Define I by replacing the t-action on M
with t_M - g_M, leaving its abelian group and involution fixed. This is an equivalence, with
inverse replacing t_M by t_M + g_M. Its underlying-sheaf comparison eI is identity. Let T be
scalar extension of I along c, so T(M) is canonically M/(t_M-g_M)M. Its right adjoint P sends H
to the same group and involution with t acting as g_H. The underlying comparison eP is identity;
the ordinary quotient adjunction gives am and the required mate equation hAdj with the quotient
insertion q. Thus all hypotheses of the first repair hold. For M=N=Z with g=-1 and t=-1,
T(M)=T(N)=Z, but M tensor_R N has t=-1 and g=+1, so T(M tensor_R N)=Z/2. The conclusion is false.
This is a mathematical counterexample, not a Lean-certified refutation.

Restore the explicit operation equations hI and hP, with eR, and scalar-extension functoriality
hTmap from the parent. They exclude this action twist and give the precise bilinear adjunction
argument of [Stacks Tag 03EL](https://stacks.math.columbia.edu/tag/03EL), using Tags 03D2 and 03D7.
The theorem remains one named proof obligation. No target or definition changes.

## Old

```lean
theorem module_pullback_tensor_iso_tail
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u})
    (c : A ⟶ S)
    (I : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A))
    (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ L)
    (T : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))
    (hT : ∀ M, T.obj M = changeOfRings c (I.obj M))
    (q : ∀ M, ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶
      ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (T.obj M)))
    (hq : ∀ (M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (W : Dᵒᵖ) (m : (I.obj M).val.obj W),
      (q M).hom.app W m =
        (eqToHom (hT M).symm).val.app W
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
              (changeOfRingsPresheaf.{u, u, u} c (I.obj M))).app W
                ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W,(c.hom.app W).hom] m))) :
    ∃ (e : ∀ M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R),
      T.obj ((monoidalCategory R).tensorObj (M) (N)) ≅
        ((monoidalCategory S).tensorObj (T.obj M) (T.obj N))),
      (∀ (M M' N N' : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).obj R)) (f : M ⟶ M') (g : N ⟶ N'),
        T.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory S).tensorHom (T.map f) (T.map g)) ∧
      ∀ (M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).obj R)) (Z : Sheaf J (Type u))
        (x : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (M)))
        (y : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (N)))
        (z : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
            (((monoidalCategory R).tensorObj (M) (N))))),
        (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
          (tensorObjIsoSheafification (M) (N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
                ((M).val ⊗ (N).val)).app W
              (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
        ∀ (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W),
          (L.map z ≫ (eI.inv.app (((monoidalCategory R).tensorObj (M) (N))) ≫ q
            (((monoidalCategory R).tensorObj (M) (N)))) ≫
            (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map
                (e M N).hom).hom.app W t =
          (tensorObjIsoSheafification (T.obj M) (T.obj N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
                ((T.obj M).val ⊗ (T.obj N).val)).app W
              ((L.map x ≫ (eI.inv.app M ≫ q M)).hom.app W t ⊗ₜ[S.obj.obj W]
                (L.map y ≫ (eI.inv.app N ≫ q N)).hom.app W t))
```

## New

```lean
theorem module_pullback_tensor_iso_tail
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (_adj : L ⊣ V) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u})
    (eR : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ≅
      L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R))
    (c : A ⟶ S)
    (I : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A))
    (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ L)
    (hI : ∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
          ∃ (addM : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
            (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
            CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
            AddCommGrpCat.{u})).obj M))
            (muM : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj M))
            (addI : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M)))
            (muI : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M))),
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose
        J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
        AddCommGrpCat.{u})).obj M)).obj.obj W),
        addM.hom.app W x = @Add.add (M.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          M)).hom.app W x) : M.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).obj.obj W),
        muM.hom.app W x = @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        addI.hom.app W x = @Add.add ((I.obj M).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M))).hom.app W x) : (I.obj M).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) :
          (I.obj M).val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        muI.hom.app W x = @SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) : A.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) : (I.obj M).val.obj W)) ∧
          L.map addM = prodComparison L ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
            ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose
            J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M ∧
          L.map muM = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
            R) ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M)
    (T : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))
    (hT : ∀ M, T.obj M = changeOfRings c (I.obj M))
    (hTmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
            R)} (f : M ⟶ N),
            T.map f ≫ eqToHom (hT N) =
              eqToHom (hT M) ≫ changeOfRingsHom c (I.obj M) (I.map f))
    (q : ∀ M, ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶
      ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (T.obj M)))
    (hq : ∀ (M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (W : Dᵒᵖ) (m : (I.obj M).val.obj W),
      (q M).hom.app W m =
        (eqToHom (hT M).symm).val.app W
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
              (changeOfRingsPresheaf.{u, u, u} c (I.obj M))).app W
                ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W,(c.hom.app W).hom] m)))
    (P : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj R))
    (eP : P ⋙ (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ V)
    (hP : ∀ H : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
          ∃ (addH : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
            (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
            CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H))
            (muH : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))
            (addP : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
              sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (muP : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (k : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ V.obj (((sheafCompose K
              (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf ((sheafCompose K (forget₂
              CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))),
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose
        K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
        AddCommGrpCat.{u})).obj H)).obj.obj W),
        addH.hom.app W x = @Add.add (H.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          H)).hom.app W x) : H.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶
          ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).obj.obj W),
        muH.hom.app W x = @SMul.smul (S.obj.obj W) (H.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj S)).hom.app W x) : S.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        addP.hom.app W x = @Add.add ((P.obj H).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H))).hom.app W x) : (P.obj H).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) :
          (P.obj H).val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        muP.hom.app W x = @SMul.smul (R.obj.obj W) ((P.obj H).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) : (P.obj H).val.obj W)) ∧
          V.map addH = prodComparison V ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H)
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ≫
            prod.map (eP.inv.app H) (eP.inv.app H) ≫ addP ≫ eP.hom.app H ∧
          k ≫ V.map (prod.fst : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
            (CategoryTheory.forget CommRingCat.{u})).obj S)) =
            (prod.fst : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
              (CategoryTheory.forget CommRingCat.{u})).obj R)) ≫
              _adj.homEquiv ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
                ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S)
                (eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map c) ∧
          k ≫ V.map (prod.snd : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
            (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H)) =
            (prod.snd : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H))) ≫ eP.hom.app H ∧
          muP ≫ eP.hom.app H = k ≫ V.map muH)
    (am : T ⊣ P)
    (hAdj : ∀ (M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R))
      (H : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
        CommRingCat.{u} RingCat.{u})).obj S)) (f : T.obj M ⟶ H),
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
          (am.homEquiv M H f) ≫ eP.hom.app H =
        _adj.homEquiv
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
          ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H)
          (eI.inv.app M ≫ q M ≫
            (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map f)) :
    ∃ (e : ∀ M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R),
      T.obj ((monoidalCategory R).tensorObj (M) (N)) ≅
        ((monoidalCategory S).tensorObj (T.obj M) (T.obj N))),
      (∀ (M M' N N' : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).obj R)) (f : M ⟶ M') (g : N ⟶ N'),
        T.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory S).tensorHom (T.map f) (T.map g)) ∧
      ∀ (M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).obj R)) (Z : Sheaf J (Type u))
        (x : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (M)))
        (y : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (N)))
        (z : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
            (((monoidalCategory R).tensorObj (M) (N))))),
        (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
          (tensorObjIsoSheafification (M) (N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
                ((M).val ⊗ (N).val)).app W
              (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
        ∀ (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W),
          (L.map z ≫ (eI.inv.app (((monoidalCategory R).tensorObj (M) (N))) ≫ q
            (((monoidalCategory R).tensorObj (M) (N)))) ≫
            (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map
                (e M N).hom).hom.app W t =
          (tensorObjIsoSheafification (T.obj M) (T.obj N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
                ((T.obj M).val ⊗ (T.obj N).val)).app W
              ((L.map x ≫ (eI.inv.app M ≫ q M)).hom.app W t ⊗ₜ[S.obj.obj W]
                (L.map y ≫ (eI.inv.app N ≫ q N)).hom.app W t))
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.ModulePullbackTensorIsoE --uses
module_pullback_tensor_iso_tail` lists 197 transitive importers and only the declaration's own
module and the parent as textual users. The other importers use the unchanged parent interface;
no definition or target statement changes meaning.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.ModulePullbackTensorIsoE` | E2 | Corrected intermediate theorem; conclusion unchanged, geometric operation hypotheses restored. |
| `Sheaf.CategoryTheory.ModulePullbackTensorIso` | NG (original author; no live claim file found) | Signature unchanged. Final call passes witnesses already constructed. Add the proof-only adjunction import formerly reexported by the tail. |

The unused public import of `TensorProductOfUniverses` is removed from the tail.
`ModulePullbackPushforwardAdjunction` is imported privately by the parent, where its theorem is
used. The tail directly publicly imports `Mathlib.Algebra.Category.Grp.FilteredColimits` for the
instances required to elaborate its scalar-extension signature. No Lean declaration from the
removed tensor-universe module occurs in either delivered signature.

## Status

landed 20261016T054833-L-155881 2026-10-16 (merge of deliver/E2/Sheaf.CategoryTheory.ModulePullbackTensorIsoE)
