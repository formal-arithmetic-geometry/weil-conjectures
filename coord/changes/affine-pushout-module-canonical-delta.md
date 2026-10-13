# AlgebraicGeometry.Scheme.Modules.affine_pushout_module_section_presentation

## Reason

The statement passed an arbitrary ring homomorphism delta while its second action
formula is valid for the canonical second inclusion. This condition was already
asserted in the original docstring but was absent from its Lean signature. In the
affine example D=k, C=k[x], G=A with N=C, E=C tensor_k C and M=C tensor_k C,
choose delta=b (the first inclusion). The first action and normalized unit force
p(x tensor 1)=x tensor 1 and p(1 tensor x)=1 tensor x. The second action at d=1,n=1
would identify these two distinct polynomials. Add exactly the equation identifying
delta with t after the ring inverse-image unit. No definition changes, no target
signature changes, and no target-definition review is reopened.

The proof now constructs the affine comparison from existing declarations and reduces
the second action to the strictly smaller scalar-compatibility equation of the
inverse-image extension unit. The second reading also proves that equation from
canonical inverse-image semilinearity and tensor balancing, leaving no new sorry.
The fully proved affine comparison is a private helper.
The local heartbeat limits allow elaboration of restricted section-module instances;
each delivered file remains within the single-file 60-second limit.

## Old

```lean
theorem affine_pushout_module_section_presentation [IsAffineHom f]
     (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
     (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app (fV V))
            ((κ.inv.app G).val.app (fV V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                (fV V)
                ((1 : B.obj.obj (fV V)) ⊗ₜ[(IA).obj.obj (fV V),(t.hom.app (fV V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V)
    (δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V))) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
      Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
    ∃ p : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) ≃ₗ[Γ(X, V)]
          ((P.obj G).val.obj (op (f ⁻¹ᵁ V))),
        (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)),
          (b.hom.app (op (f ⁻¹ᵁ V))).hom c • p (d ⊗ₜ[Γ(X, V)] n) =
          p ((c * d) ⊗ₜ[Γ(X, V)] n)) ∧
        (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)), δ c • p (d ⊗ₜ[Γ(X, V)] n) =
          p (d ⊗ₜ[Γ(X, V)] (c • n))) ∧
        ∀ n, p ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n) =
          (κ.inv.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n)
```

## New

```lean
theorem affine_pushout_module_section_presentation [IsAffineHom f]
     (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
     (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app (fV V))
            ((κ.inv.app G).val.app (fV V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                (fV V)
                ((1 : B.obj.obj (fV V)) ⊗ₜ[(IA).obj.obj (fV V),(t.hom.app (fV V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V)
    (δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)))
    (hδ : δ = (t.hom.app (op (f ⁻¹ᵁ V))).hom.comp
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).unit.app A).hom.app (op V)).hom) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
      Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
    ∃ p : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) ≃ₗ[Γ(X, V)]
          ((P.obj G).val.obj (op (f ⁻¹ᵁ V))),
        (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)),
          (b.hom.app (op (f ⁻¹ᵁ V))).hom c • p (d ⊗ₜ[Γ(X, V)] n) =
          p ((c * d) ⊗ₜ[Γ(X, V)] n)) ∧
        (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)), δ c • p (d ⊗ₜ[Γ(X, V)] n) =
          p (d ⊗ₜ[Γ(X, V)] (c • n))) ∧
        ∀ n, p ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n) =
          (κ.inv.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n)
```

The only signature change is the added hdelta binder. All existing declaration visibility and the signature of
affine_pushout_first_tensor_sections remain identical. The second reading removes
the unused public List.Basic import from the parent; the sole name user imports
List.Basic explicitly, and no signature needs it. The sole caller must explicitly retain the canonical delta: obtaining an
arbitrary witness from the old ring-section existence statement loses that equation.
It therefore repeats the already proved ring-presentation calculation locally for
the explicit delta, using the same affine ring-section pushout. This is forced glue,
not a new mathematical dependency or an extra public declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffinePushoutModuleSectionPresentation | W2 | Corrected non-target signature and proof. |
| Sheaf.AlgebraicGeometry.AffinePushoutFirstTensorSections | unclaimed | Forced proof-only adaptation: select the canonical delta, prove its retraction and generation with the existing ring-section pushout, pass rfl for hdelta. Existing signature and visibility stay identical. |

The downstream name search reports these two modules, including the declaration's
own module. All transitive importers retain their existing signatures and use the
unchanged affine_pushout_first_tensor_sections interface. No other forced adaptations.

## Status

landed 20261013T082422-L-1651008 2026-10-13 (merge of deliver/W2/Sheaf.AlgebraicGeometry.AffinePushoutModuleSectionPresentation)
