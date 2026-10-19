/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.HomologySequence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology

/-!
# Testing finite Tor amplitude at the residue field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-trace-perfectness/
`lem-exc-residue-tor-test.md` (blueprint: lem-exc-residue-tor-test).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Padic

/-- The residue field coefficient as an `A`-module, where `A` is the finite coefficient ring.
Source: blueprint `lem-exc-residue-tor-test` (blueprint: lem-exc-residue-tor-test). -/
noncomputable def coefficientExtensionResidueModule
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n) :=
  ModuleCat.of (Padic.coefficientExtensionRing l E n)
    ((Padic.coefficientExtensionRing l E n) ⧸
      Ideal.span ({Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionRing l E n)))

end Padic

namespace AlgebraicGeometry.Etale

/-- Tor amplitude over `A = 𝒪_E/(ϖ_E^n)` is tested by the residue constant sheaf.

Source: Weil blueprint, smooth purity, trace perfectness, order 1823
(blueprint: lem-exc-residue-tor-test).

Proof:
1. By [lem-weil-l-adic-extension-integers-dvr], $\mathcal O_E$ has maximal ideal $(\varpi_E)$ and
finite residue field. By [lem-weil-valued-dvr-finite-quotients], $A$ is finite local with maximal
ideal $(\varpi_E)/(\varpi_E^n)$. Thus $\kappa$ is the field $\mathcal O_E/(\varpi_E)$, and
$\varpi_E^n=0$ in $A$. The constant-sheaf construction [def-weil-pbc-constant-sheaf] and exactness
of sheafification [lem-weil-pbc-site-module-presheaf-sheafification-exact], applied to the
constant-presheaf sequence $A\xrightarrow{\varpi_E}A\to\kappa\to0$, identify $A_T/\varpi_E A_T$
with $\kappa_T$. A sheaf of $A_T$-modules killed by $\varpi_E$ therefore has a unique
$\kappa_T$-module structure: locally write a section of the quotient ring as the image of a
section of $A_T$ and let it act using that lift; different lifts differ by $\varpi_E A_T$ and act
identically.
2. If $K$ has Tor amplitude in $[a,b]$, take $\mathcal M=\kappa_T$ in the definition [def-kun-tor-
amplitude]. This gives exactly the asserted cohomology vanishing.
3. Conversely assume the asserted vanishing. Apply [lem-pc-kflat-resolution] on the ringed site
$(T_{\Et},A_T)$ to a representative of $K$, obtaining a K-flat resolution $P\to K$ with every term
$P^q$ flat. By [def-kun-derived-tensor], for any $A_T$-module sheaf $M$ in degree zero,
$P\otimes_{A_T}M$ represents $K\otimes_A^L M$. Put $C=P\otimes_{A_T}\kappa_T$, a complex of
$\kappa_T$-modules. The hypothesis says $\mathcal H^i(C)=0$ outside $[a,b]$. No boundedness of $P$
or $C$ is assumed.
4. Let $N$ be any $\kappa_T$-module sheaf. Regard $C^q$ and $N$ as presheaves of modules over the
constant presheaf $U\mapsto\kappa$. For each $U$, tensoring $\kappa$-vector spaces with $N(U)$ is
exact: a short exact sequence splits after lifting a basis of its quotient, and its tensor is
again a split sequence. The tensor functor is additive, so these split sequences identify kernels
and images after tensoring. Apply this to $0\to Z^i\to C^i(U)\to B^{i+1}\to0$ and $0\to B^i\to
Z^i\to H^i(C(U))\to0$, with $Z^i$ and $B^i$ the cycles and boundaries of $C(U)$. It follows that
the canonical map $[z]\otimes y\mapsto[z\otimes y]$ is an isomorphism $$H^i(C(U))\otimes_\kappa
N(U)\simeq H^i(C(U)\otimes_\kappa N(U)).$$ This map is natural in restrictions even though the
splittings used to prove bijectivity need not be. By [lem-pc-sites-module-sheafification-tensor],
sheafifying the sectionwise tensor over the constant presheaf $\kappa$ gives
$C\otimes_{\kappa_T}N$. By [lem-weil-pbc-site-module-presheaf-sheafification-exact],
sheafification commutes with cohomology. Sheafify the displayed isomorphism and apply the tensor
comparison again, obtaining $$\mathcal H^i(C\otimes_{\kappa_T}N)\simeq\mathcal
H^i(C)\otimes_{\kappa_T}N.$$ In particular this vanishes outside $[a,b]$. The balanced maps
$(x\otimes t)\otimes y\mapsto x\otimes ty$ and $x\otimes y\mapsto(x\otimes1)\otimes y$ are
balanced over the indicated rings and commute with restrictions and differentials. Sections of a
sheaf tensor product are locally sums of pure tensors, so these formulas define local maps on
generators; balancing makes them independent of representatives, and sheafification glues them.
Their composites fix each pure tensor, hence every local section; the sheaf tensor construction
[def-pur-sheaf-tensor-product] therefore gives an isomorphism of complexes
$$(P\otimes_{A_T}\kappa_T)\otimes_{\kappa_T}N\simeq P\otimes_{A_T}N.$$ Thus $\mathcal
H^i(P\otimes_{A_T}N)=0$ outside $[a,b]$. The calculation uses the field $\kappa$, not the
generally non-field ring $\kappa_T(U)$.
5. For an arbitrary $A_T$-module sheaf $M$ put $F_sM=\operatorname{im}(\varpi_E^s:M\to M)$, $0\leq
s\leq n$. Then $F_0M=M$ and $F_nM=0$. Write $G_s=F_sM/F_{s+1}M$. Multiplication by $\varpi_E$
sends $F_sM$ into $F_{s+1}M$: locally its section is $\varpi_E^s m$, and its product is
$\varpi_E^{s+1}m$. Hence $G_s$ is killed by $\varpi_E$, so step 1 makes it a $\kappa_T$-module
sheaf and step 4 applies to $G_s$. This is a finite filtration for every $M$, including sheaves
without any finiteness or constructibility condition.
6. For $0\leq s<n$, tensor the short exact sequence $0\to F_{s+1}M\to F_sM\to G_s\to0$ termwise
with $P$. Each $P^q$ is flat, so [def-pc-flat-sheaf-modules], with the elementary symmetry
$x\otimes y\mapsto y\otimes x$, gives a short exact sequence of complexes. By [lem-weil-pbc-
complex-ses-homology-long-exact], $$\mathcal H^i(P\otimes F_{s+1}M)\longrightarrow\mathcal
H^i(P\otimes F_sM)\longrightarrow\mathcal H^i(P\otimes G_s)$$ is exact. Fix $i\notin[a,b]$.
Descending induction on $s$ starts at $F_nM=0$. At the induction step the left group is zero by
induction and the right group is zero by step 4, so the middle group is zero. At $s=0$ this proves
$\mathcal H^i(P\otimes M)=0$. By [def-kun-derived-tensor] this is $\mathcal H^i(K\otimes_A^L
M)=0$. Since $M$ and $i\notin[a,b]$ were arbitrary, [def-kun-tor-amplitude] proves the converse
with exactly the same interval.
-/
theorem residue_tor_amplitude_test
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T)
    (hK : @DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn) T K) :
    DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) T a b K ↔
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero
          ((_root_.DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) i).obj
            (((derivedTensor
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf T.smallEtaleTopology
                    (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
                  (Padic.coefficientExtensionResidueModule l E n))))) := by
  sorry

end AlgebraicGeometry.Etale
