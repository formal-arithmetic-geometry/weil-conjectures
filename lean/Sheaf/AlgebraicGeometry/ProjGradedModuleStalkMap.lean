/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# ProjGradedModuleStalkMap

Source: Stacks Project, Constructions, Section 01M3, stalk computation before
Definition 01M6 (blueprint: lem-weil-pbc-proj-graded-module-stalk-map).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-graded-module-sheaf-stalks) -/
local instance localizedScalarsProjGradedModuleStalkMap (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "T[" x "]" => (x).asHomogeneousIdeal.toIdeal.primeCompl
local notation "Rp[" x "]" => HomogeneousLocalization 𝒜 T[x]
local notation "Np[" x "]" => LocalizedModule T[x] M
local notation "ModX" => SheafOfModules (moduleRings (Proj 𝒜).toRingedSpace)

/-- The canonical additive map from chart germs to equal-degree prime-localized fractions.
No injectivity or surjectivity is asserted here.
Source: Stacks Project, Constructions, Section 01M3, stalk computation before
Definition 01M6 (definition-structure-sheaf-proj).
(blueprint: lem-weil-pbc-proj-graded-module-stalk-map)

Proof:
1. On a positive homogeneous chart containing x, include powers of its denominator into
   the prime complement and apply the ordinary localized-module map. Equal-degree
   representatives show that its restriction lands in Zp, using hZ and hZp.
2. Each rho agrees with this map: write a fraction as y/f^m and use the given relation
   g^e=a*f. The image of a^m*y/g^(e*m) equals y/f^m by clearing denominators in the
   prime localization. This holds for every representative by localization equality.
3. Positive standard opens form a basis. Every stalk element has a chart representative;
   two representatives of the same germ agree on a smaller positive standard open.
   The compatibility in step 2 makes the value independent of both choices. Addition
   is checked after restricting two sections to their common product chart. This
   constructs an additive map, not a choice of an arbitrary existence witness.
4. Represent the scalar and section germ on a common positive standard open. A scalar
   section there is awayToSection of a homogeneous localized scalar. The chart scalar
   law and awayToSection_germ identify its image under stalkIso with that scalar's
   prime localization, proving semilinearity. Step 1 gives the formula for every chart
   fraction, without requiring its numerator itself to be homogeneous.
-/
theorem gradedModuleStalkMap
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (hZ : (∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)))
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (hlaws : (∀ (f g : Fidx) (i : D[g] ≤ D[f]),
        (∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) ∧
        (∀ (r : R[f]) (q : Z f), rho f g i (r • q) = rhoS f g i r • rho f g i q) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g.val.1 ^ e = a * f.val.1 →
          ∀ (m : ℕ) (y : M) (q : Z f),
            (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
            (rho f g i q : N[g]) = mk (a ^ m • y)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1))) ∧
      (∀ (f : Fidx) (i : D[f] ≤ D[f]) (q : Z f), rho f f i q = q) ∧
      (∀ (f g h : Fidx) (i : D[g] ≤ D[f]) (j : D[h] ≤ D[g]) (q : Z f),
        rho g h j (rho f g i q) = rho f h (j.trans i) q) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]), D[f] = D[g] →
        Function.Bijective (rho f g i)))
    (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hchart : (∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
        alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]) (s : F.val.obj (op D[f])),
        alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)))
    (Zp : ∀ x : Proj 𝒜, Submodule Rp[x] Np[x])
    (hZp : ∀ x : Proj 𝒜, (Zp x : Set Np[x]) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M)) T[x]) :
    ∃ (tau : ∀ x : Proj 𝒜,
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F →+ Zp x),
      (∀ (x : Proj 𝒜) (r : (Proj 𝒜).presheaf.stalk x)
        (s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F),
        tau x (r • s) = (stalkIso 𝒜 x).hom r • tau x s) ∧
      (∀ (x : Proj 𝒜) (f : Fidx) (hx : x ∈ D[f]) (m : ℕ) (y : M)
        (q : Z f) (t : T[x]),
        (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
        (t : S) = f.val.1 ^ m →
        (tau x (TopCat.Presheaf.germ F.val.presheaf D[f] x hx
          ((alpha f).symm q)) : Np[x]) = mk y t) := by sorry

end AlgebraicGeometry.Proj
