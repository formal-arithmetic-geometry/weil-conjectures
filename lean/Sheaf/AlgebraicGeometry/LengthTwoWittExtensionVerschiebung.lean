module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The two-coordinate Witt extension and its canonical Verschiebung

Source: Milne, Algebraic Groups (2017), Section 11(j), pp. 226–227, Proposition 11.44
and the following paragraph (blueprint: lem-sfb-length-two-witt-extension-verschiebung).
The index two counts coordinates. All polynomial maps are actual constructions.
The canonical Verschiebung is computed using the recorded invariant-tensor construction,
with an explicitly characterized Frobenius-twist identification, including over imperfect fields.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.LengthTwoWitt

noncomputable section

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [hk : CharP k p]

/-- The reduction of the integral correction polynomial; division takes place in ℕ before
casting to k. Source: Milne, p. 226, S₁
(blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def correction : MvPolynomial (Fin 2) k :=
  -∑ i ∈ Finset.Ico 1 p,
    MvPolynomial.C ((p.choose i / p : ℕ) : k) *
      MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (p - i)

/-- Evaluation of the integral correction in any commutative k-algebra, with no reducedness
assumption. Source: Milne, p. 226, S₁
(blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def correctionValue {R : Type v} [CommRing R] [Algebra k R] (a b : R) : R :=
  MvPolynomial.aeval ![a, b] (correction k p)

/-- The affine plane Spec k[X₀,X₁]. Source: Milne, pp. 226–227
(blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def scheme (_p : ℕ) : Over (Spec (.of k)) :=
  StandardGroupSchemes.affine k (MvPolynomial (Fin 2) k)

/-- Witt comultiplication, giving exactly the displayed addition on every algebra-valued
point. Source: Milne, p. 226, S₀ and S₁
(blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def comul : MvPolynomial (Fin 2) k →ₐ[k]
    MvPolynomial (Fin 2) k ⊗[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval
    ![MvPolynomial.X 0 ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X 0,
      MvPolynomial.X 1 ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X 1 +
        correctionValue k p
          ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ⊗ₜ[k] 1)
          (1 ⊗ₜ[k] MvPolynomial.X 0)]

/-- The zero point (0,0). Source: Milne, pp. 226–227
(blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def counit : MvPolynomial (Fin 2) k →ₐ[k] k := MvPolynomial.aeval ![0, 0]

/-- The inverse (a,b) ↦ (-a,-b-cₚ(a,-a)). Source: Milne, pp. 226–227
(blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def antipode : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![-MvPolynomial.X 0,
    -MvPolynomial.X 1 - correctionValue k p (MvPolynomial.X 0) (-MvPolynomial.X 0)]

include hp hk in
/-- The unique group structure with precisely the specified polynomial operations.
Source: Milne, Proposition 11.43, pp. 226–227
(blueprint: lem-sfb-length-two-witt-extension-verschiebung).

Proof: p divides choose(p,i) for 0<i<p, since neither i! nor (p-i)! is divisible by p.
Over ℤ the correction C satisfies pC=X^p+Y^p-(X+Y)^p. Expanding this identity in three
variables and cancelling p coefficientwise proves the cocycle identity. Symmetry and
C(X,0)=C(0,X)=0 hold termwise. Reduction to k proves coassociativity, both counit identities,
and both antipode identities on X₀,X₁. The Hopf spectrum functor then gives the group law;
its three structure maps determine the group object uniquely. -/
theorem group_existsUnique :
    ∃! g : GrpObj (scheme k p),
      g.one = StandardGroupSchemes.identitySection k (counit k) ∧
      g.mul = StandardGroupSchemes.multiplication k (comul k p) ∧
      g.inv = StandardGroupSchemes.map k (antipode k p) := by
  sorry

/-- The uniquely determined polynomial Witt group law; only its verification is postponed.
Source: Milne, Proposition 11.43 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
noncomputable instance group : GrpObj (scheme k p) :=
  (group_existsUnique k p).exists.choose

/-- The inclusion t ↦ (0,t), induced by its polynomial substitution.
Source: Milne, Proposition 11.44 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def inclusion : StandardGroupSchemes.additive k ⟶ scheme k p :=
  StandardGroupSchemes.map k (MvPolynomial.aeval ![0, Polynomial.X])

/-- The first-coordinate truncation (a,b) ↦ a.
Source: Milne, Proposition 11.44 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def truncation : scheme k p ⟶ StandardGroupSchemes.additive k :=
  StandardGroupSchemes.map k (Polynomial.aeval (MvPolynomial.X 0))

/-- The shift followed by truncation (a,b) ↦ (0,a), on coordinates.
Source: Milne, p. 227 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
def shiftCoordinates : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![0, MvPolynomial.X 0]

/-- Commutativity, finite type, and the exact extension with its geometric properties.
Source: Milne, Proposition 11.44, p. 227
(blueprint: lem-sfb-length-two-witt-extension-verschiebung).

Proof: symmetry of C gives commutativity; the two generators give finite type, and an
endowed affine scheme is quasi-compact. The substitutions j* and τ* preserve the Hopf maps
on generators. j* is surjective with kernel (X₀), hence j is a closed immersion. The fibre
ring of τ over zero is k[X₀,X₁]⊗_{k[t]}k = k[X₀,X₁]/(X₀) ≃ k[X₁]; its group law and
inclusion are precisely Gₐ and j, so this identifies the scheme-theoretic kernel.
The projection is a polynomial extension by X₁, hence flat. The scheme section a↦(a,0)
proves surjectivity. One generator and no relations give local finite presentation; the
affine projection is quasi-compact and quasi-separated, hence finitely presented. -/
theorem extension :
    IsCommMonObj (scheme k p) ∧
    LocallyOfFiniteType (scheme k p).hom ∧ QuasiCompact (scheme k p).hom ∧
    IsMonHom (inclusion k p) ∧ IsMonHom (truncation k p) ∧
    IsClosedImmersion (inclusion k p).left ∧
    (∃ e : StandardGroupSchemes.additive k ≅ GrpObj.ker (truncation k p),
      e.hom ≫ GrpObj.kerι (truncation k p) = inclusion k p) ∧
    Flat (truncation k p).left ∧ Surjective (truncation k p).left ∧
    LocallyOfFinitePresentation (truncation k p).left ∧
    QuasiCompact (truncation k p).left ∧ QuasiSeparated (truncation k p).left := by
  sorry

/-- The polynomial affine plane is affine.
Source: Milne, p. 227 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
instance isAffine : IsAffine (scheme k p).left :=
  inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin 2) k))))

/-- The recorded additive affine line is affine.
Source: Milne, p. 227 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
instance additiveIsAffine : IsAffine (StandardGroupSchemes.additive k).left :=
  inferInstanceAs (IsAffine (Spec (.of (Polynomial k))))

/-- The canonical Hopf structure attached to the specified Witt group.
Source: Milne, p. 227 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
noncomputable instance coordinateHopf : HopfAlgebra k Γ((scheme k p).left, ⊤) :=
  letI := specOverSpec (R := .of k) (A := .of (MvPolynomial (Fin 2) k))
  letI : GrpObj ((scheme k p).left.asOver (Spec (.of k))) := group k p
  HopfAction.coordinateHopfAlgebra k (scheme k p).left

/-- The canonical Hopf structure attached to the recorded additive group.
Source: Milne, p. 227 (blueprint: lem-sfb-length-two-witt-extension-verschiebung). -/
noncomputable instance additiveCoordinateHopf :
    HopfAlgebra k Γ((StandardGroupSchemes.additive k).left, ⊤) :=
  letI := specOverSpec (R := .of k) (A := .of (Polynomial k))
  letI : GrpObj ((StandardGroupSchemes.additive k).left.asOver (Spec (.of k))) :=
    StandardGroupSchemes.additiveGroup k
  HopfAction.coordinateHopfAlgebra k (StandardGroupSchemes.additive k).left

/-- Canonical Verschiebung is the shift (0,a) under the coefficient-Frobenius twist
identification. The formula on every global coordinate, rather than just rational points,
identifies the canonical scheme map from the dependency's invariant-tensor construction.
Source: Milne, p. 227, paragraph after Proposition 11.44
(blueprint: lem-sfb-length-two-witt-extension-verschiebung).

Proof: the twist isomorphism sends f⊗c to c f^[p], where only coefficients are raised to p.
Its inverse fixes k and sends Xᵢ to Xᵢ⊗1. The tensor balancing relation shows both composites
are identities, without inverting Frobenius on k. The structure polynomials lie in Fₚ,
so this is the canonical group-scheme twist identification. The n-fold sum over ℤ is
(na,nb+((n-n^p)/p)a^p), by induction using the correction polynomial; setting n=p and
reducing to k gives [p](a,b)=(0,a^p). Relative Frobenius has coordinate substitution
Xᵢ↦Xᵢ^p, injective on the monomial basis. The shift U has UF=[p], and the canonical
V supplied by lem-sfb-affine-group-frobenius-verschiebung has VF=[p]. Cancel the injective
Frobenius comorphism to obtain U=V. Transport through ΓSpecIso gives the displayed formula
for the dependency's actual projection composed with iterated comultiplication. -/
theorem canonical_verschiebung :
    ∃ e : AffineGroupFrobeniusVerschiebung.twist k p Γ((scheme k p).left, ⊤) ≃ₐ[k]
        MvPolynomial (Fin 2) k,
      (∀ (a : Γ((scheme k p).left, ⊤)) (c : k),
        e (AffineGroupFrobeniusVerschiebung.pure k p Γ((scheme k p).left, ⊤) a c) =
          MvPolynomial.C c * MvPolynomial.map (frobenius k p)
            ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).hom.hom a)) ∧
      (∀ a : Γ((scheme k p).left, ⊤),
        e (AffineGroupFrobeniusVerschiebung.projection k p Γ((scheme k p).left, ⊤)
          (AffineGroupFrobeniusVerschiebung.iteratedComul k Γ((scheme k p).left, ⊤) p a)) =
            shiftCoordinates k ((Scheme.ΓSpecIso
              (.of (MvPolynomial (Fin 2) k))).hom.hom a)) := by
  sorry

/-- The canonical Verschiebung of Gₐ is zero, using its canonical twist identification.
Source: Milne, p. 227 (blueprint: lem-sfb-length-two-witt-extension-verschiebung).

Proof: the same twist isomorphism sends f⊗c to c f^[p] in k[X]. The additive group has
[p]=0. Its relative Frobenius comorphism X↦X^p is injective on monomials, so VF=0
forces the canonical V to be the zero group homomorphism. Its coordinate map is evaluation
at zero, including on nonreduced algebra-valued points and in characteristic two. -/
theorem additive_canonical_verschiebung :
    ∃ e : AffineGroupFrobeniusVerschiebung.twist k p
        Γ((StandardGroupSchemes.additive k).left, ⊤) ≃ₐ[k] Polynomial k,
      (∀ (a : Γ((StandardGroupSchemes.additive k).left, ⊤)) (c : k),
        e (AffineGroupFrobeniusVerschiebung.pure k p
          Γ((StandardGroupSchemes.additive k).left, ⊤) a c) =
            Polynomial.C c * Polynomial.map (frobenius k p)
              ((Scheme.ΓSpecIso (.of (Polynomial k))).hom.hom a)) ∧
      (∀ a : Γ((StandardGroupSchemes.additive k).left, ⊤),
        e (AffineGroupFrobeniusVerschiebung.projection k p
          Γ((StandardGroupSchemes.additive k).left, ⊤)
          (AffineGroupFrobeniusVerschiebung.iteratedComul k
            Γ((StandardGroupSchemes.additive k).left, ⊤) p a)) =
              Polynomial.aeval (0 : Polynomial k)
                ((Scheme.ΓSpecIso (.of (Polynomial k))).hom.hom a)) := by
  sorry

end

end AlgebraicGeometry.LengthTwoWitt
