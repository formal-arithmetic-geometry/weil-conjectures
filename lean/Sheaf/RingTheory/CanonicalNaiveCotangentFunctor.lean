module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # The canonical naive cotangent functor over a fixed ring

Source: Stacks Project, Algebra, Tags 00S0 and 07BQ, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor).

The conormal and differential are Mathlib's canonical presentation. The basis
of polynomial differentials identifies its target with the free module on the
underlying algebra. The mapping cone of the degree-zero single differential
places these terms in degrees minus one and zero, as in the existing
`Algebra.indEtale_naiveCotangent_acyclic` interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CanonicalNaiveCotangent

variable {R : Type u} [CommRing R]

/-- The canonical augmentation ideal in R[T]. Source: Stacks, Tag 00S0
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
abbrev ideal (T : CommAlgCat.{max u v} R) : Ideal (MvPolynomial T R) :=
  (Generators.self R T).toExtension.ker

/-- The differential in free coordinates, on the actual ideal conormal quotient.
Source: Stacks, Tag 00S0 (blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def differential (T : CommAlgCat.{max u v} R) :
    ModuleCat.of R (ideal T).Cotangent ⟶ ModuleCat.of R (T →₀ T) :=
  ModuleCat.ofHom
    (((Generators.self R T).cotangentSpaceBasis.repr.toLinearMap.comp
        (Generators.self R T).toExtension.cotangentComplex).restrictScalars R ∘ₗ
      (LinearEquiv.toLinearMap
        (Generators.self R T).toExtension.cotangentEquivCotangentKer.symm).restrictScalars R)

/-- Renaming the variable [t] as [u(t)] carries the augmentation kernel into the
augmentation kernel. Source: Stacks, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor).
Proof: evaluation after renaming is u after evaluation, by the polynomial
universal property on constants and variables. Thus a kernel element evaluates
in the target to u(0) = 0. -/
theorem rename_mem {T T' : CommAlgCat.{max u v} R} (f : T ⟶ T') :
    ideal T ≤ (ideal T').comap (MvPolynomial.rename f.hom) := by
  sorry

/-- The conormal map [g] ↦ [rename u g], using the existing quotient map.
Source: Stacks, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def conormalMap {T T' : CommAlgCat.{max u v} R} (f : T ⟶ T') :
    ModuleCat.of R (ideal T).Cotangent ⟶ ModuleCat.of R (ideal T').Cotangent :=
  ModuleCat.ofHom (Ideal.mapCotangent (ideal T) (ideal T')
    (MvPolynomial.rename f.hom) (rename_mem f))

/-- The free-module map a d[t] ↦ u(a) d[u(t)], adding coefficients when labels
collide. Source: Stacks, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def freeMap {T T' : CommAlgCat.{max u v} R} (f : T ⟶ T') :
    ModuleCat.of R (T →₀ T) ⟶ ModuleCat.of R (T' →₀ T') :=
  ModuleCat.ofHom (Finsupp.lsum R (fun t : T ↦
    ((Finsupp.lsingle (f t) : T' →ₗ[T'] (T' →₀ T')).restrictScalars R).comp
      f.hom.toLinearMap))

/-- The two prescribed maps commute with the cotangent differential.
Source: Stacks, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor).
Proof: both derivatives vanish on R, send [t] to d[u(t)], and satisfy Leibniz
with coefficients evaluated by u. Expand a polynomial into monomials. The
product rule gives equality, including sums at colliding labels. It vanishes
on the kernel square, hence descends to the conormal quotient. -/
theorem differential_naturality {T T' : CommAlgCat.{max u v} R} (f : T ⟶ T') :
    conormalMap f ≫ differential T' = differential T ≫ freeMap f := by
  sorry

/-- The actual commuting square of the canonical differentials.
Source: Stacks, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def differentialMap {T T' : CommAlgCat.{max u v} R} (f : T ⟶ T') :
    Arrow.mk (differential T) ⟶ Arrow.mk (differential T') :=
  Arrow.homMk (conormalMap f) (freeMap f) (differential_naturality f)

/-- The canonical naive complex, formed with the existing single and cone
constructions. Source: Stacks, Tag 00S0
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def complex (T : CommAlgCat.{max u v} R) : CochainComplex (ModuleCat.{max u v} R) ℤ :=
  CochainComplex.mappingCone
    ((HomologicalComplex.single (ModuleCat.{max u v} R) (.up ℤ) 0).map (differential T))

/-- The canonical chain map induced by the prescribed conormal and free maps.
Source: Stacks, equation-functoriality-NL
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def map {T T' : CommAlgCat.{max u v} R} (f : T ⟶ T') : complex T ⟶ complex T' :=
  HomologicalComplex.homotopyCofiber.mapArrowHom _ _
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    ((HomologicalComplex.single (ModuleCat.{max u v} R) (.up ℤ) 0).mapArrow.map
      (differentialMap f))

/-- Identity law of the prescribed chain maps. Source: Stacks, Tag 07BQ
(blueprint: def-sfb-canonical-naive-cotangent-functor).
Proof: identity renaming fixes conormal representatives and free generators.
Thus its differential square is the identity. Apply the single functor and
Mathlib's identity law for the induced map of homotopy cofibers. -/
theorem map_id (T : CommAlgCat.{max u v} R) : map (𝟙 T) = 𝟙 (complex T) := by
  sorry

/-- Composition law of the prescribed chain maps. Source: Stacks, Tag 07BQ
(blueprint: def-sfb-canonical-naive-cotangent-functor).
Proof: successive renaming is composite renaming on every polynomial variable.
On a free generator a d[t], the composite is v(u(a)) d[v(u(t))], including
collisions. Therefore the differential squares compose; apply the single
functor and Mathlib's composition law for maps of homotopy cofibers. -/
theorem map_comp {T T' T'' : CommAlgCat.{max u v} R} (f : T ⟶ T') (g : T' ⟶ T'') :
    map (f ≫ g) = map f ≫ map g := by
  sorry

/-- The canonical two-term naive cotangent functor, restricted to R-modules.
Source: Stacks, Tags 00S0 and 07BQ
(blueprint: def-sfb-canonical-naive-cotangent-functor). -/
def functor (R : Type u) [CommRing R] :
    CommAlgCat.{max u v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ where
  obj := complex
  map := map
  map_id := map_id
  map_comp := map_comp

end Algebra.CanonicalNaiveCotangent
