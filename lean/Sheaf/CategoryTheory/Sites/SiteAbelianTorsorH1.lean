module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Abelian torsors and derived first cohomology on a general site

Source: Stacks Project, Cohomology on Sites, Tags 01FT, 03AH and 03AJ
(blueprint: lem-sfb-site-abelian-torsor-h1).

The coefficient universe `max u v w` contains both site universes and an arbitrary
additional universe. No terminal object in the site is required. The extension is a
concrete pushout of the free abelian pair-difference and displacement maps. The theorem
specifies its augmentation, its torsor fibre, the boundary-of-one classification,
the formula for every extension, and addition through the contracted quotient.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification of abelian presheaves in any universe containing both site universes.
This is Mathlib sheafification transported through its essentially small site interface.
Source: Stacks Project, Sites, Tag 00WH.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
instance siteAbelianSheafify : HasSheafify J AddCommGrpCat.{max u v w} :=
  haveI : EssentiallySmall.{max u v w} C := essentiallySmallSelf C
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{max u v w}

/-- Sheafification of set presheaves in the same coefficient universe, for orbit quotients.
Source: Stacks Project, Sites, Tag 00WH.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
instance siteTypeSheafify : HasSheafify J (Type (max u v w)) :=
  haveI : EssentiallySmall.{max u v w} C := essentiallySmallSelf C
  hasSheafifyEssentiallySmallSite J (Type (max u v w))

/-- Abelian sheaves on the site form a Grothendieck category in the coefficient universe.
Mathlib then supplies enough injectives and injective resolutions, without a final object.
Source: Stacks Project, Injectives, Tag 079H; Cohomology on Sites, Tag 01FT.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
instance siteAbelianSheafGrothendieck :
    IsGrothendieckAbelian.{max u v w} (Sheaf J AddCommGrpCat.{max u v w}) :=
  haveI : EssentiallySmall.{max u v w} C := essentiallySmallSelf C
  Sheaf.isGrothendieckAbelian_of_essentiallySmall J AddCommGrpCat.{max u v w}

variable {G : Sheaf J AddCommGrpCat.{max u v w}} (T : Torsor G)

/-- The sheafification of the sectionwise free abelian group on the torsor.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, free abelian sheaf paragraph.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteFreeSheaf :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).obj (T.sheaf.obj ⋙ AddCommGrpCat.free)

/-- The free abelian sheaf on pairs of torsor sections.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, pair-difference generators.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteRelations :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).obj (T.pairs ⋙ AddCommGrpCat.free)

/-- The sheafified map sending `(x,y)` to `[y] - [x]`.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, kernel of augmentation.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteDifference : siteRelations J T ⟶ siteFreeSheaf J T :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).map T.pairsDiff

/-- The sheafified map sending `(x,y)` to the unique `g` with `g + x = y`.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, the map from pair differences.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable def siteDisplacement : siteRelations J T ⟶ G :=
  (sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ G |>.symm <| T.pairsSub

/-- The concrete quotient extension: push out pair differences along displacement.
The pushout is the quotient of `G ⊕ ℤ[T]` by `(g,[t]-[g+t])`: taking the pair
`(t,g+t)` gives that relation, and every pair is of this form by simple transitivity.
This is the free-relation presentation of the pushout in Tag 03AJ, not a choice from
a mere existence assertion. Source: Stacks Project, Cohomology on Sites, Tag 03AJ.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteExtension : Sheaf J AddCommGrpCat.{max u v w} :=
  pushout (siteDifference J T) (siteDisplacement J T)

/-- The canonical map from the coefficient sheaf to the concrete torsor extension.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, lower exact row.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteInclusion : G ⟶ siteExtension J T :=
  pushout.inr (C := Sheaf J AddCommGrpCat.{max u v w}) (siteDifference J T) (siteDisplacement J T)

/-- The canonical map from the free abelian sheaf to the torsor extension.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, pushout square.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteGenerators : siteFreeSheaf J T ⟶ siteExtension J T :=
  pushout.inl (C := Sheaf J AddCommGrpCat.{max u v w}) (siteDifference J T) (siteDisplacement J T)

/-- The constant integer presheaf, with integers lifted to the coefficient universe.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, constant integer sheaf.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
abbrev siteIntegerPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max u v w} ℤ))

/-- The sheafification of the constant integer presheaf.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, constant integer sheaf.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable abbrev siteIntegers : Sheaf J AddCommGrpCat.{max u v w} :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).obj (siteIntegerPresheaf.{u, v, w} (C := C))

/-- The generator `[t]` in the concrete torsor extension, defined through the sheafification unit.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, free abelian sheaf and pushout.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable def siteGenerator (U : Cᵒᵖ) (t : T.sheaf.obj.obj U) :
    (siteExtension J T).obj.obj U :=
  (siteGenerators J T).hom.app U
    ((toSheafify J (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (FreeAbelianGroup.of t))

/-- The section `1` of the constant integer sheaf over any object of the site.
Source: Stacks Project, Cohomology on Sites, Tag 03AJ, boundary-of-one construction.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable def siteOneSection (U : Cᵒᵖ) : (siteIntegers.{u, v, w} J).obj.obj U :=
  (toSheafify J (siteIntegerPresheaf.{u, v, w} (C := C))).app U ⟨1⟩

/-- The global section `1` of the constant integer sheaf, using the constant/global-sections unit.
Its restrictions are `siteOneSection`; it requires no final object of the site.
Source: Stacks Project, Cohomology on Sites, Tags 01FT and 03AJ.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable def siteOne : (Γ J AddCommGrpCat.{max u v w}).obj
    (siteIntegers.{u, v, w} J) :=
  (constantSheafΓAdj J AddCommGrpCat.{max u v w}).unit.app
    (AddCommGrpCat.of (ULift.{max u v w} ℤ)) ⟨1⟩

/-- The actual derived global-section connecting map of a short exact sequence in degree zero.
Use the standard derived-category constructions, and precompose the connecting morphism
with the canonical map from global sections to their zeroth right derived functor.
Source: Stacks Project, Cohomology on Sites, Tags 01FT and 03AJ; Derived Categories, Tag 015B.
(blueprint: lem-sfb-site-abelian-torsor-h1). -/
noncomputable def siteBoundary
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max u v w})} (hS : S.ShortExact) :
    (Γ J AddCommGrpCat.{max u v w}).obj S.X₃ →
      ((Γ J AddCommGrpCat.{max u v w}).rightDerived 1).obj S.X₁ :=
  letI := HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{max u v w})
  letI := HasDerivedCategory.standard AddCommGrpCat.{max u v w}
  fun x ↦ hS.rightDerivedδ (Γ J AddCommGrpCat.{max u v w}) 0
    ((Γ J AddCommGrpCat.{max u v w}).toRightDerivedZero.app S.X₃ x)

/-- Abelian torsors are classified by derived first global-section cohomology, with the
specified free-relation extension, the formula for every extension, and the group law.
Source: Stacks Project, Cohomology on Sites, Tags 01FT, 03AH and 03AJ.
(blueprint: lem-sfb-site-abelian-torsor-h1).

Proof:
1. Global sections are compatible families, hence additive and left exact, without a final
   site object. Abelian sheaves have enough injectives. The universal right-derived
   delta-functor and the resolution of an injective by itself show that for an injective
   embedding `G → I`, with quotient `Q`, the connecting map `Γ(Q) → H¹(G)` is surjective
   with kernel the image of `Γ(I)` (lem-weil-pbc-site-sheaves-enough-injectives,
   lem-weil-pbc-right-derived-universal-delta-functor, lem-sp-derived-well-defined).
2. The concrete pushout imposes `[g+t] = g + [t]`. Over an object with a torsor section
   `t₀`, its coordinates are `(a, Σ nₜ[t]) ↦ (a + Σ nₜ d(t,t₀), Σ nₜ)`, inverse to
   `(a,n) ↦ j(a) + n[t₀]`. These maps respect the relations and all restrictions.
   Exact sheafification extends the local coordinates to the sheaf quotient. Thus the
   inclusion is monic, its image is the augmentation kernel, and the augmentation is
   locally surjective, hence epic. The generators identify the torsor equivariantly
   with its fibre over one (lem-weil-pbc-sheafification-exact,
   lem-weil-pbc-site-sheafification-sections-local,
   lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective,
   lem-galois-set-sheaf-local-bijection-isomorphism).
3. For any extension by the integer sheaf, local lifts of one differ uniquely by a
   section of `G`; hence its fibre is a torsor. The map from the canonical extension of
   this fibre to the given extension sends `g` to `i(g)` and `[e]` to `e`. It is the
   identity in the local coordinates of step 2. Torsor isomorphisms also induce
   extension isomorphisms. Naturality of the connecting map therefore gives a
   well-defined class on isomorphism classes and the arbitrary-extension formula.
4. For the fixed injective embedding of step 1, let `L_q` be the torsor of lifts of a
   global section `q` of `Q`. Its canonical extension maps to `I`, by `g ↦ i(g)` and
   `[x] ↦ x`; the quotient map sends one to `q`. Naturality gives class `δ(q)`.
   Surjectivity of the connecting map proves surjectivity of the classification.
5. Injectivity of `I` extends `G → I` across `G → E_T` to `b : E_T → I`.
   The images in `Q` of `b([t])` are invariant under torsor translation. Local sections
   and the sheaf axiom glue them to a compatible global family `q`. The map
   `t ↦ b([t])` identifies `T` with `L_q`, as is checked in the local coordinates.
6. Equal cohomology classes give `q' - q = r(a)` for a global section `a` of `I` by
   exactness in step 1. Translation by `a` identifies `L_q` with `L_q'`, proving
   injectivity. The definition by the canonical extension uses no injective embedding,
   so the bijection is canonical.
7. The generator `[0]` of the trivial torsor gives a global lift of one, so its boundary
   is zero by exactness.
8. For two torsors form the sheafification of the antidiagonal orbit presheaf. Locally
   write `t = g+t₀`, `t' = h+t₀'`; its orbit coordinate is `g+h`. Thus the residual
   action is translation and the quotient is a torsor, with the stated universal
   property. The map `(t,t') ↦ b([t]) + b'([t'])` is invariant under the antidiagonal
   action and factors through the sheafified quotient, identifying it with `L_(q+q')`.
   Additivity of the connecting homomorphism gives the asserted sum formula. -/
theorem site_abelian_torsor_h1 (G : Sheaf J AddCommGrpCat.{max u v w}) :
    ∃ κ : _root_.Quotient (Torsor.setoid (G := G)) →
        ((Γ J AddCommGrpCat.{max u v w}).rightDerived 1).obj G,
      Function.Bijective κ ∧
      (∀ T : Torsor G,
        ∃ (p : siteExtension J T ⟶ siteIntegers.{u, v, w} J)
          (hp : siteInclusion J T ≫ p = 0)
          (hS : (ShortComplex.mk (siteInclusion J T) p hp).ShortExact),
          (∀ (U : Cᵒᵖ) (t : T.sheaf.obj.obj U),
            p.hom.app U (siteGenerator J T U t) = siteOneSection J U) ∧
          (∀ U : Cᵒᵖ, ∃ e : T.sheaf.obj.obj U ≃
              {x : (siteExtension J T).obj.obj U | p.hom.app U x = siteOneSection J U},
            ∀ t : T.sheaf.obj.obj U, (e t).val = siteGenerator J T U t) ∧
          (∀ (U : Cᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U),
            siteGenerator J T U (T.vadd U g t) =
              (siteInclusion J T).hom.app U g + siteGenerator J T U t) ∧
          κ ⟦T⟧ = siteBoundary J hS (siteOne J)) ∧
      (∀ (E : Sheaf J AddCommGrpCat.{max u v w}) (i : G ⟶ E)
        (p : E ⟶ siteIntegers.{u, v, w} J) (hp : i ≫ p = 0)
        (hS : (ShortComplex.mk i p hp).ShortExact),
        ∃ (P : Torsor G)
          (e : ∀ U : Cᵒᵖ,
            P.sheaf.obj.obj U ≃ {x : E.obj.obj U | p.hom.app U x = siteOneSection J U}),
          (∀ (U V : Cᵒᵖ) (f : U ⟶ V) (t : P.sheaf.obj.obj U),
            (e V (P.sheaf.obj.map f t)).val = E.obj.map f (e U t).val) ∧
          (∀ (U : Cᵒᵖ) (g : G.obj.obj U) (t : P.sheaf.obj.obj U),
            (e U (P.vadd U g t)).val = i.hom.app U g + (e U t).val) ∧
          κ ⟦P⟧ = siteBoundary J hS (siteOne J)) ∧
      κ ⟦trivial G⟧ = 0 ∧
      (∀ T T' : Torsor G, ∃ (S : Torsor G)
        (q : ∀ U : Cᵒᵖ, T.sheaf.obj.obj U → T'.sheaf.obj.obj U → S.sheaf.obj.obj U),
        (∀ (U V : Cᵒᵖ) (f : U ⟶ V) (t : T.sheaf.obj.obj U)
          (t' : T'.sheaf.obj.obj U),
          S.sheaf.obj.map f (q U t t') =
            q V (T.sheaf.obj.map f t) (T'.sheaf.obj.map f t')) ∧
        (∀ (U : Cᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
          (t' : T'.sheaf.obj.obj U),
          q U (T.vadd U g t) (T'.vadd U (-g) t') = q U t t') ∧
        (∀ (U : Cᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
          (t' : T'.sheaf.obj.obj U),
          q U (T.vadd U g t) t' = S.vadd U g (q U t t')) ∧
        (∀ (F : Sheaf J (Type (max u v w)))
          (a : ∀ U : Cᵒᵖ, T.sheaf.obj.obj U → T'.sheaf.obj.obj U → F.obj.obj U)
          (_hn : ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (t : T.sheaf.obj.obj U)
            (t' : T'.sheaf.obj.obj U),
            F.obj.map f (a U t t') =
              a V (T.sheaf.obj.map f t) (T'.sheaf.obj.map f t'))
          (_hi : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
            (t' : T'.sheaf.obj.obj U),
            a U (T.vadd U g t) (T'.vadd U (-g) t') = a U t t'),
          ∃! l : S.sheaf ⟶ F, ∀ (U : Cᵒᵖ) (t : T.sheaf.obj.obj U)
            (t' : T'.sheaf.obj.obj U), l.hom.app U (q U t t') = a U t t') ∧
        κ ⟦S⟧ = κ ⟦T⟧ + κ ⟦T'⟧) := by
  sorry

end CategoryTheory.Sheaf.Torsor
