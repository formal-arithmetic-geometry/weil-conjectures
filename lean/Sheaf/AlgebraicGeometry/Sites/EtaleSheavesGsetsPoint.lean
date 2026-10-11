/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.AlgebraicGeometry.EtaleFieldGsets

/-!
# Étale sheaves and discrete Galois sets

Source: Stacks Project, Tag 03QT and the Galois action on stalks in Tag 03QW
(blueprint: lem-exc-etale-sheaves-gsets-point).
-/

universe u v

open CategoryTheory
open AlgebraicGeometry
open Opposite

namespace AlgebraicGeometry

/-
The theorem packages the two assertions of the node. `DiscreteContAction` (with the
discrete topology on sets from `hasForget₂TypeTopCat`, as in `etaleFieldGsets`) is the
category of `Gal(Ksep/K)`-sets with every stabilizer open for the Krull topology.
-/
/--
(blueprint: lem-exc-etale-sheaves-gsets-point) Let `K` be a field, let `Ksep`
be a separable closure embedded in an algebraic closure `Ω` of `K`, and let
`s : Spec Ω ⟶ Spec K` be the corresponding geometric point.  Étale sheaves on
`Spec K` are equivalent, via the stalk at `s`, to discrete continuous actions
of `Gal(Ksep/K)`, and the stalk of the representable sheaf of an étale scheme
`X` is naturally `Hom_K(Spec Ksep, X)`.

The proof follows the four steps of the DAG node, using Stacks Tags 03QW and 03QT.
1. Represent germs by pointed-neighbourhood triples
   (`def-weil-pbc-geometric-stalks`) and change the lift by an extension of the
   Galois automorphism. Finite separable residue fields
   (`lem-weil-pbc-etale-fibre-discrete-separable-points`) give independence of
   that extension and an open subgroup contained in each stabilizer.
2. Representables are sheaves (`lem-weil-pbc-small-etale-representable-presheaf-sheaf`).
   Evaluate their stalks (`lem-galois-stalk-representable`), and use the finite
   separable components (`lem-weil-pbc-etale-fibre-discrete-separable-points`)
   to identify Omega-points with Ksep-points, naturally and equivariantly.
3. Sections over finite separable extensions are stabilizer invariants
   (`lem-exc-field-sections-stalk-invariants`), compatibly with embeddings.
   The component decomposition (`lem-weil-pbc-etale-fibre-discrete-separable-points`)
   and the sheaf condition give sections as products. Equivariant stalk maps
   therefore reconstruct sheaf morphisms, proving full faithfulness.
4. Realize each discrete Galois set by an etale scheme
   (`lem-exc-etale-field-gsets`). Step 2 gives its representable sheaf the
   required stalk, proving essential surjectivity and hence the equivalence.
-/
theorem etaleSheavesGsetsPoint
    (K Ksep Ω : Type u)
    [Field K] [Field Ksep] [Field Ω]
    [Algebra K Ksep] [Algebra K Ω]
    [IsSepClosure K Ksep] [IsAlgClosed Ω] [IsAlgClosure K Ω]
    (i : Ksep →ₐ[K] Ω) :
    ∃ E : Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
        (Type (max u (v + 1))) ≌
        DiscreteContAction (Type (max u (v + 1))) (Gal(Ksep / K)),
      ∃ η : E.functor ⋙
            forget₂ (DiscreteContAction (Type (max u (v + 1))) (Gal(Ksep / K)))
              (Type (max u (v + 1))) ≅
          (Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber,
      (∀ (F : Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
            (Type (max u (v + 1))))
          (X : (Scheme.Spec.obj (op (.of K))).Etale)
          (l l' : Scheme.Spec.obj (op (.of Ω)) ⟶ X.left)
          (h : l ≫ X.hom = Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)
          (h' : l' ≫ X.hom = Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)
          (g : Gal(Ksep / K)) (τ : Ω ≃ₐ[K] Ω)
          (_hτ : τ.toAlgHom.comp i = i.comp g.toAlgHom)
          (_hl : l' = Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op ≫ l)
          (t : F.obj.obj (op X)),
        (η.hom.app F)
          (((E.functor.obj F).obj.obj.ρ g)
            ((η.inv.app F) ((Scheme.pointSmallEtale
              (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).toPresheafFiber
                X (Over.homMk l h) F.obj t))) =
          (Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).toPresheafFiber
              X (Over.homMk l' h') F.obj t) ∧
      ∃ e : ∀ (X : (Scheme.Spec.obj (op (.of K))).Etale),
          ((Scheme.pointSmallEtale
              (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.obj
                (((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X) :
                  Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                    (Type (max u (v + 1))))) ≃
            {f : Scheme.Spec.obj (op (.of Ksep)) ⟶ X.left //
              f ≫ X.hom = Scheme.Spec.map
                (CommRingCat.ofHom (algebraMap K Ksep)).op},
        (∀ (X : (Scheme.Spec.obj (op (.of K))).Etale)
          (g : Gal(Ksep / K))
            (x : (Scheme.pointSmallEtale
              (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.obj
                (((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X) :
                  Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                    (Type (max u (v + 1))))),
            ((e X) ((η.hom.app ((Scheme.smallEtaleTopology
              (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X :
                Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                  (Type (max u (v + 1)))))
                (((E.functor.obj ((Scheme.smallEtaleTopology
                  (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X)).obj.obj.ρ g)
                  (η.inv.app ((Scheme.smallEtaleTopology
                  (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X :
                    Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                      (Type (max u (v + 1)))) x)))).val =
              Scheme.Spec.map (CommRingCat.ofHom g.toRingHom).op ≫ ((e X) x).val) ∧
        ∀ (X Y : (Scheme.Spec.obj (op (.of K))).Etale) (f : X ⟶ Y)
          (x : (Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.obj
              (((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X) :
                Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                  (Type (max u (v + 1))))),
          ((e Y) ((Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.map
              ((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.map f)
              x)).val = ((e X) x).val ≫ f.left := by
  sorry

end AlgebraicGeometry
