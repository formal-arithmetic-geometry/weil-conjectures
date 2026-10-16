module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Topology.Spectral.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Every nonempty closed subset `C` of a scheme proper over `Spec A` meets the
closed fibre over `V(I)` when `I` lies in the Jacobson radical: the image of `C` is closed, so
it contains a closed point of `Spec A`, i.e. a maximal ideal, which contains `I`. This is the
nonemptiness half of `AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`. -/
theorem Scheme.Hom.nonempty_inter_preimage_zeroLocus {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    [IsProper p] {C : Set Y} (hC : IsClosed C) (hne : C.Nonempty) :
    (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)).Nonempty := by
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ :=
    (p.isClosedMap C hC).exists_closed_singleton (hne.image p)
  have hmax : (p y : PrimeSpectrum A).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hx
  refine ⟨y, hy, ?_⟩
  change (I : Set A) ⊆ (p y : PrimeSpectrum A).asIdeal
  exact fun a ha ↦ Ideal.mem_sInf.mp (hI ha) ⟨bot_le, hmax⟩


end AlgebraicGeometry
