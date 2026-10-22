module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import Sheaf.Paper.AffineSpaceCoordinateBoundaries
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

/-! # Coordinate Thom map for the affine zero section

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 1, 3 and 5 (blueprint: def-pur-affine-space-thom-map).

## Main definitions

- `supportedClass`: the actual ordered supported coordinate-boundary product.
- `thom`: its image under the canonical closed exceptional Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineLinePurity VectorIntegrationSite

/-- Reuse the recorded compactification of the standard affine projection.
Source: proof Step 1 (blueprint: def-pur-affine-space-thom-map). -/
instance projection_compactification (B : Scheme.{u}) (c : ℕ) :
    HasCompactification (iteratedAffineLineProj B c) :=
  (AffineSpacePurity.projection_geometry B c).2

/-- The ordered tensor power of shifted finite Tate lines with its coefficient unit.
Source: the product display (blueprint: def-pur-affine-space-thom-map). -/
abbrev target (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (c : ℕ) : D P n X :=
  (AffineSpacePurity.action
    ((AffineSpacePurity.tensor (setting P n).Coefficient X).flip.obj
      (AffineSpacePurity.shiftedLine (setting P n) X)) c).obj (unit P n X)

/-- The literal successive scheme-theoretic intersections of coordinate supports.
Source: the supported cup prescription (blueprint: def-pur-affine-space-thom-map). -/
def supportData (B : Scheme.{u}) (c : ℕ) :
    List (Fin c) → Σ S : Scheme.{u}, S ⟶ iteratedAffineLine B c
  | [] => ⟨_, 𝟙 _⟩
  | i :: is => ⟨pullback (supportData B c is).2 (inclusion B c i),
      cupIntersection (supportData B c is).2 (inclusion B c i)⟩

/-- The actual intersection scheme. Source: supported cup prescription
(blueprint: def-pur-affine-space-thom-map). -/
abbrev support (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) := (supportData B c is).1

/-- The actual intersection immersion. Source: supported cup prescription
(blueprint: def-pur-affine-space-thom-map). -/
abbrev supportMap (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) := (supportData B c is).2


/-- Every partial coordinate intersection is closed. Source: proof Step 5
(blueprint: def-pur-affine-space-thom-map).
Proof: the empty intersection is the identity. Each successor is a pullback
of a closed coordinate immersion followed by a closed immersion. -/
theorem support_closed (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) :
    IsClosedImmersion (supportMap B c is) := by
  sorry
attribute [instance] support_closed

/-- Boundedness of every finite tensor power of the shifted locally free Tate line.
Source: proof Steps 1 and 5 (blueprint: def-pur-affine-space-thom-map).
Proof: the ordinary root line is etale locally a free module of rank one because
ell is invertible. It is flat, as are its tensor powers. Thus the tensor power
is a sheaf shifted by 2c and is bounded below; exact comparison preserves this. -/
theorem target_plus (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    DerivedCategory.TStructure.t.plus (target P n X c) := by
  sorry

/-- The one-factor shifted line is bounded below. Source: proof Steps 1--3
(blueprint: def-pur-affine-space-thom-map).
Proof: the ordinary finite Tate line is a sheaf in degree zero. Shift by two
preserves boundedness below, as does the exact site comparison. -/
theorem boundary_plus (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (AffineSpacePurity.shiftedLine (setting P n) X) := by
  sorry

/-- Apply the recorded supportedCup at degrees zero and cancel the zero-shift
unitors. This uses the published operation itself. Source: proof Step 5
(blueprint: def-pur-affine-space-thom-map). -/
def cupZero (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (α : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ F.obj)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)) ⟶ G.obj) :
    (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (pullback i j))) ⟶ cupTensorObject P X F.obj G.obj :=
  letI : X.Over (Spec (.of P.field.k)) := ⟨aX⟩
  supportedCup P i j F G 0 0
      (α ≫ (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app F.obj)
      (β ≫ (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app G.obj) ≫
    (shiftFunctorZero (CupDerivedCategory P X) ℤ).hom.app
      (cupTensorObject P X F.obj G.obj)

/-- The degree-zero object supported on a literal partial coordinate intersection.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
@[irreducible]
def classSource (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) (is : List (Fin c)) : D P n (iteratedAffineLine B c) :=
  (cupSingle (setting P n) (iteratedAffineLine B c)).obj
    ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (supportMap B c is)).obj
      ((setting P n).constant (support B c is)))

/-- Unfold the named partial-support object once, without choosing an identification.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: this is the defining equation of classSource. -/
theorem classSource_eq (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) (is : List (Fin c)) :
    classSource P n B c is =
      (cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (supportMap B c is)).obj
          ((setting P n).constant (support B c is))) := by
  sorry

/-- The empty support intersection is the whole affine space with its identity map.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: unfold classSource, support, supportMap and the empty equation of supportData. -/
theorem classSource_nil (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (c : ℕ) :
    classSource P n B c [] =
      (cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
          (𝟙 (iteratedAffineLine B c))).obj
            ((setting P n).constant (iteratedAffineLine B c))) := by
  sorry

/-- The successor support is exactly the scheme-theoretic cup intersection.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: unfold classSource, support and supportMap and reduce the cons equation
of supportData. Both sides are the same sheaf on the same pullback scheme. -/
theorem classSource_cons (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) (i : Fin c) (is : List (Fin c)) :
    classSource P n B c (i :: is) =
      (cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
          (cupIntersection (supportMap B c is) (inclusion B c i))).obj
            ((setting P n).constant (pullback (supportMap B c is) (inclusion B c i)))) := by
  sorry

/-- The successor target is the same tensor product used by supportedCup.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: unfold target and the successor equation of AffineSpacePurity.action.
The two tensor symbols refer to the same canonical derived monoidal structure. -/
theorem target_succ (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (d : ℕ) :
    cupTensorObject (setting P n) X (target P n X d)
      (AffineSpacePurity.shiftedLine (setting P n) X) = target P n X (d + 1) := by
  sorry

/-- The ordered product of the actual coordinate Cartier boundaries. The empty
product is the constant-unit identity; each successor is the recorded supported cup.
The equality transports only unfold its literal support and tensor endpoints.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
@[irreducible]
def product (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) : (is : List (Fin c)) →
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length :=
  List.rec (motive := fun is : List (Fin c) ↦
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length)
    (eqToHom (classSource_nil P n B c) ≫
      (cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
          (iteratedAffineLine B c)).hom.app
            ((setting P n).constant (iteratedAffineLine B c))))
    (fun i is previous ↦ eqToHom (classSource_cons P n B c i is) ≫
      cupZero (setting P n) (AffineSpacePurity.towerBase aB c)
        (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (AffineSpacePurity.towerBase aB c) is.length⟩
        ⟨AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c),
          boundary_plus P n _⟩
        (eqToHom (classSource_eq P n B c is).symm ≫ previous)
        (boundary P n B aB c i) ≫
      eqToHom (target_succ P n (iteratedAffineLine B c) is.length))

/-- All the coordinate equations cut out exactly the zero section, canonically over X.
Source: proof Steps 1 and 5 (blueprint: def-pur-affine-space-thom-map).
Proof: on every affine chart the successive pullback quotient is the polynomial
ring modulo all coordinates, hence the base ring. The quotient identifications
fix constants and kill every generator, so glue over the base. They identify the
closed immersion with zero. Any two such isomorphisms agree after composing
with the monomorphism zero, which proves uniqueness. This includes c=0. -/
theorem supportIso_existsUnique (B : Scheme.{u}) (c : ℕ) :
    ∃! e : support B c (List.finRange c) ≅ B,
      e.hom ≫ zero B c = supportMap B c (List.finRange c) := by
  sorry

/-- The unique support identification over the affine space, not an arbitrary iso.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
def supportIso (B : Scheme.{u}) (c : ℕ) : support B c (List.finRange c) ≅ B :=
  (supportIso_existsUnique B c).exists.choose

/-- The supported product on the zero section itself, transported by its unique
scheme-theoretic support identification. Coordinates have even degree, so this
right-associated enumeration agrees with the specified ordered product.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
def supportedClass (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c :=
  (cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec) ≫
    eqToHom (classSource_eq P n B c (List.finRange c)).symm ≫
    product P n B aB c (List.finRange c) ≫
    eqToHom (congrArg (target P n (iteratedAffineLine B c)) (@List.length_finRange c))


/-- The coefficient unit is bounded below of etale origin.
Source: proof Step 1 (blueprint: def-pur-affine-space-thom-map).
Proof: it is comparison inverse image of the constant sheaf in degree zero.
The exact comparison preserves the lower bound zero. -/
theorem unit_origin (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (setting P n).Coefficient) X
      (unit P n X) := by
  sorry

/-- Closed direct image is exact for this Noetherian coordinate immersion.
Source: proof Step 3 (blueprint: def-pur-affine-space-thom-map).
Proof: finite type over k makes X Noetherian, so the complementary open is
quasi-compact. The open-closed exactness theorem applies to this complementary
pair and gives preservation of finite colimits. -/
theorem zero_exact (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)) := by
  sorry

/-- Proper compact support followed by exact closed direct image in degree zero.
Every arrow is the canonical derived or compactification comparison.
Source: proof Steps 3 and 5 (blueprint: def-pur-affine-space-thom-map). -/
def closedSingleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj M) :=
  (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) i).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategorySingleFunctor 0).app M

/-- The Thom morphism is the exceptional adjunct of the actual supported cup product.
No purity isomorphism is selected in defining its data.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
@[irreducible]
def thom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    unit P n B ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B c)).obj (target P n (iteratedAffineLine B c) c) :=
  letI := zero_exact P n B aB c
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n (iteratedAffineLine B c) (AffineSpacePurity.towerBase aB c) c)
    ((closedSingleIso (setting P n).Coefficient (zero B c)
      ((setting P n).constant B)).hom ≫ supportedClass P n B aB c)


end AlgebraicGeometry.ProEtale.AffineZeroPurity
