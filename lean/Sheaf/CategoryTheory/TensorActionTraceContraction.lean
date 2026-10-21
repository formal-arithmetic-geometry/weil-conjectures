module

public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Free.Coherence

/-!
# Contraction of two traces through tensor actions

Source: the final canonical-reassociations sentence of
`sec-smooth-purity/sk-thm-smooth-purity/lem-pur-projection-purity-agreement.proof.md`
in the blueprint snapshot `main-20261015`, expanded into the coefficient-contraction
calculation (blueprint: lem-pur-tensor-action-trace-contraction).

The domain predicates allow projection isomorphisms on full permitted domains only.
No adjunction, braiding, or compositor for the two functors is required.
-/

@[expose] public section

universe uX uY uZ vX vY vZ

namespace CategoryTheory

open MonoidalCategory

/-- Contract an inverse projection map with a specified map to the tensor unit.
This is the displayed definition of `d` in the coefficient-contraction expansion of
the blueprint's canonical-reassociations sentence in
`lem-pur-projection-purity-agreement.proof.md`, snapshot `main-20261015`
(blueprint: lem-pur-tensor-action-trace-contraction).
The construction is the actual composite `q`, then `t ⊗ 1`, then the left unitor. -/
def tensorTraceContraction {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {T A B : C} (q : T ⟶ A ⊗ B) (t : A ⟶ 𝟙_ C) : T ⟶ B :=
  q ≫ (t ⊗ₘ 𝟙 B) ≫ (λ_ B).hom

/-- Successive contractions of arbitrary trace maps factor through the iterated inverse
projection isomorphisms. Source: the coefficient-contraction expansion of the final
canonical-reassociations sentence of `lem-pur-projection-purity-agreement.proof.md`,
blueprint snapshot `main-20261015` (blueprint: lem-pur-tensor-action-trace-contraction).

`Df` and `Dg` specify the full domains of the supplied isomorphisms. Naturality is required
for every pair of arrows between permitted pairs. The five membership hypotheses say
exactly that all projection components in the calculation are permitted. The tensor-action
equation is imposed wherever its three components are permitted. `PfMonoidal.μIso.inv`
is the inverse tensor comparison delta; the mapped composite at the start of the right
side of the conclusion is sigma. The object `L` is written out as `Lf ⊗ Pf.obj Lg`.

Proof plan:
1. Invert the tensor-action equation at `Lf`, `Lg`, `Pg.obj K`. This expresses the inverse
   projection at their tensor product using the associator, the two inverse projections,
   and `Ff.map sigma`.
2. Move `tf` through the associator by naturality. Monoidal structural coherence
   (`lem-coef-monoidal-structural-coherence`, Stacks Tag 0HAY(2)) identifies the left unitor
   on a tensor product after the associator with the left unitor on its first factor.
3. Contract the equality of step 1. Tensor bifunctoriality gives the first contraction as
   `Ff.map sigma`, then the inverse projection at `L`, then `a ⊗ 1`, where `a = d_f,Lg`.
4. Invert the naturality square for `PFg` at `a` and the identity of `K`. This moves
   `Fg.map (a ⊗ 1)` past the inverse projection for `g`; no tensor-action law for `g` is used.
5. Apply `Fg` to step 3 and postcompose with the second contraction. Step 4 and tensor
   bifunctoriality combine the trace factors into `Fg.map a ≫ tg`, which is `b`.
All substitutions use only the displayed permitted components and their full-domain arrows.
-/
theorem tensorAction_trace_contraction
    {X : Type uX} [Category.{vX} X] [MonoidalCategory X]
    {Y : Type uY} [Category.{vY} Y] [MonoidalCategory Y]
    {Z : Type uZ} [Category.{vZ} Z] [MonoidalCategory Z]
    (Ff : X ⥤ Y) (Fg : Y ⥤ Z) (Pf : Y ⥤ X) (Pg : Z ⥤ Y)
    (PfMonoidal : Pf.CoreMonoidal) (_PgMonoidal : Pg.CoreMonoidal)
    (Df : X → Y → Prop) (Dg : Y → Z → Prop)
    (PFf : ∀ (M : X) (N : Y), Df M N → (Ff.obj M ⊗ N ≅ Ff.obj (M ⊗ Pf.obj N)))
    (PFg : ∀ (M : Y) (N : Z), Dg M N → (Fg.obj M ⊗ N ≅ Fg.obj (M ⊗ Pg.obj N)))
    (_hf_natural : ∀ (M M' : X) (N N' : Y) (h : Df M N) (h' : Df M' N')
      (r : M ⟶ M') (s : N ⟶ N'),
      (Ff.map r ⊗ₘ s) ≫ (PFf M' N' h').hom =
        (PFf M N h).hom ≫ Ff.map (r ⊗ₘ Pf.map s))
    (_hg_natural : ∀ (M M' : Y) (N N' : Z) (h : Dg M N) (h' : Dg M' N')
      (r : M ⟶ M') (s : N ⟶ N'),
      (Fg.map r ⊗ₘ s) ≫ (PFg M' N' h').hom =
        (PFg M N h).hom ≫ Fg.map (r ⊗ₘ Pg.map s))
    (_hf_action : ∀ (M : X) (N N' : Y)
      (h : Df M N) (h' : Df (M ⊗ Pf.obj N) N') (h'' : Df M (N ⊗ N')),
      (PFf M (N ⊗ N') h'').hom =
        (α_ (Ff.obj M) N N').inv ≫ ((PFf M N h).hom ⊗ₘ 𝟙 N') ≫
          (PFf (M ⊗ Pf.obj N) N' h').hom ≫
            Ff.map ((α_ M (Pf.obj N) (Pf.obj N')).hom ≫
              (M ◁ (PfMonoidal.μIso N N').hom)))
    (Lf : X) (Lg : Y) (tf : Ff.obj Lf ⟶ 𝟙_ Y) (tg : Fg.obj Lg ⟶ 𝟙_ Z)
    (K : Z)
    (hfl : Df Lf Lg) (hft : Df Lf (Lg ⊗ Pg.obj K))
    (hfs : Df (Lf ⊗ Pf.obj Lg) (Pg.obj K))
    (hgl : Dg Lg K) (hgc : Dg (Ff.obj (Lf ⊗ Pf.obj Lg)) K) :
    Fg.map (tensorTraceContraction (PFf Lf (Lg ⊗ Pg.obj K) hft).inv tf) ≫
        tensorTraceContraction (PFg Lg K hgl).inv tg =
      Fg.map (Ff.map ((Lf ◁ (PfMonoidal.μIso Lg (Pg.obj K)).inv) ≫
          (α_ Lf (Pf.obj Lg) (Pf.obj (Pg.obj K))).inv)) ≫
        Fg.map (PFf (Lf ⊗ Pf.obj Lg) (Pg.obj K) hfs).inv ≫
          (PFg (Ff.obj (Lf ⊗ Pf.obj Lg)) K hgc).inv ≫
            ((Fg.map (tensorTraceContraction (PFf Lf Lg hfl).inv tf) ≫ tg) ⊗ₘ 𝟙 K) ≫
              (λ_ K).hom := by
  sorry

end CategoryTheory
