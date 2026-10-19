/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.RelativeAssassin
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.RingTheory.FibrePrimesResidueFields
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.RingTheory.AssociatedPrimeMinimalOfDepth
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.FlatPullbackAssociatedPoints
import Sheaf.RingTheory.TensorFieldsCohenMacaulay

/-!
# Relative associated points under arbitrary base change

Source: Stacks Project, Divisors, Tag 05DC, `lemma-base-change-relative-assassin`
(blueprint: lem-trf-relative-assassin-base-change).

The relative assassin uses element annihilators in the fibre-module stalks. The residual
spectrum and its distinguished point are Mathlib's `Triplet.tensor` and `SpecOfPoint`.
Applying pullback symmetry orders the tensor factors as κ(r') ⊗[κ(r)] κ(z), exactly as
in the source. `Triplet.tensor` is the pushout of the canonical residue-field maps in
commutative rings, hence the usual algebra tensor product with its usual multiplication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Under arbitrary base change, fibrewise association is equivalent to association of
the image and genericity in an irreducible component of the residual tensor spectrum.
No finite generation of the module, flatness of the original morphisms, or Noetherian
hypothesis on the base is required.

Source: Stacks Project, Divisors, Tag 05DC, `lemma-base-change-relative-assassin`
(blueprint: lem-trf-relative-assassin-base-change).

Proof plan, following the nine steps of the node:

1. Put $k=\kappa(r)$, $k'=\kappa(r')$, $Y=X_r$ and $Y'=X'_{r'}$. By
[lem-weil-pbc-fibre-of-base-change] there is a cartesian square identifying $h:Y'\to Y$ with the
base change of $\operatorname{Spec}k'\to\operatorname{Spec}k$. If $i:Y\to X$ and $i':Y'\to X'$ are
the fibre projections, then $i\circ h=g'\circ i'$. Pullback composition in
[def-pc-module-pullback] therefore gives $\mathcal F'_{r'}=(i')^*(g')^*\mathcal F\cong
h^*i^*\mathcal F=h^*\mathcal F_r$. This comparison identifies the same pullback module, rather
than changing the coefficient sheaf.

2. The map $\operatorname{Spec}k'\to\operatorname{Spec}k$ is flat by
[lem-pc-field-extension-flat]. Its base change $h$ is flat by
[lem-weil-pbc-flat-morphism-base-change]. No flatness of the original morphism $f$ or of $g$ is
required.

3. The structure map $Y\to\operatorname{Spec}k$ is locally of finite type by
[lem-weil-pbc-lft-base-change]. A field has only the ideals $(0)$ and $(1)$, so its spectrum is
locally Noetherian. Apply [pqf-lem-locnoeth-lft] to conclude that $Y$ is locally Noetherian. The
sheaf $\mathcal F_r=i^*\mathcal F$ is quasi-coherent by
[lem-weil-pbc-module-pullback-quasi-coherent]. Thus the flat pullback formula can be applied with
base $Y$ and arbitrary quasi-coherent coefficients $\mathcal F_r$; no finite generation of
$\mathcal F$ has been assumed.

4. Apply [lem-trf-flat-pullback-associated-points] to $h:Y'\to Y$ and $\mathcal G=\mathcal F_r$,
using steps 1–3. It gives $$\operatorname{Ass}_{Y'}(\mathcal
F'_{r'})=\bigcup_{y\in\operatorname{Ass}_Y(\mathcal F_r)}j_y\operatorname{Ass}_{Y'_y}(\mathcal
O_{Y'_y}).$$ The point of $Y$ underlying $z'\in Y'$ is the canonical point $z\in X_r$. Since the
images of the fibre maps $j_y$ lie over their respective $y$, this equality says precisely that
$z'$ is associated to $\mathcal F'_{r'}$ if and only if $z$ is associated to $\mathcal F_r$ and
the corresponding point of $Y'_z$ is associated to $\mathcal O_{Y'_z}$.

5. The residue field at the canonical point $z\in Y=X_r$ is $\kappa(z)$: on affine charts, clause
(2) of [lem-weil-pbc-fibre-ring-primes-residue-fields] identifies the residue field in the fibre
ring with that of the original point. Base-changing the square of step 1 along
$\operatorname{Spec}\kappa(z)\to Y$, the fibre $Y'_z$ is consequently
$\operatorname{Spec}k'\times_{\operatorname{Spec}k}\operatorname{Spec}\kappa(z)$. By
[lem-weil-pbc-fibre-product-affine-spectra] it is $\operatorname{Spec}T$ for
$T=k'\otimes_k\kappa(z)$. To check the finiteness needed below, choose an affine neighbourhood
$V=\operatorname{Spec}R$ of $r$ and a finite-type affine chart $U=\operatorname{Spec}B$ of
$f^{-1}(V)$ containing $z$, as in [def-weil-finite-type-morphism]. Apply
[lem-weil-pbc-finite-type-residue-field-extension-finitely-generated] to $R\to B$ and the primes
of $r,z$. It gives that $\kappa(z)/k$ is finitely generated as a field, even when $z$ is not
closed.

6. Apply [lem-trf-tensor-fields-cohen-macaulay] to $k'/k$ and $\kappa(z)/k$, the latter finitely
generated by step 5. Thus $T$ is Noetherian and every $T_{\mathfrak q}$ is Noetherian local
Cohen–Macaulay. The other extension $k'/k$ may be completely arbitrary. We now determine the
associated points of $\operatorname{Spec}T$ directly in these local rings.

7. Let $\mathfrak q\in\operatorname{Spec}T$ be an associated point of its structure sheaf. By
[lem-weil-pbc-affine-open-stalk-localization](c) its local ring is $T_{\mathfrak q}$; association
means its maximal ideal $\mathfrak qT_{\mathfrak q}$ is an element-annihilator associated prime of
that ring. Step 6 and [lem-weil-pbc-cm-local-associated-prime-minimal] imply that $\mathfrak
qT_{\mathfrak q}$ is a minimal prime of $T_{\mathfrak q}$. The inclusion-preserving prime
correspondence [lem-weil-pbc-primes-of-localization](1) now implies that $\mathfrak q$ is minimal
in $T$: a strictly smaller prime would extend to a strictly smaller prime below $\mathfrak
qT_{\mathfrak q}$, a contradiction.

8. Conversely, if $\mathfrak q$ is a minimal prime of $T$, the Noetherian hypothesis from step 6
lets us apply [lem-weil-pbc-noetherian-minimal-prime-associated]: $\mathfrak q$ is an
element-annihilator associated prime of $T$. By
[lem-weil-pbc-associated-prime-localization-depth-zero], its extension $\mathfrak qT_{\mathfrak
q}$ is associated to $T_{\mathfrak q}$. The stalk identification
[lem-weil-pbc-affine-open-stalk-localization](c) therefore says that $\mathfrak q$ is an
associated point of the structure sheaf of $\operatorname{Spec}T$. Together with step 7 this
characterizes those associated points as exactly the minimal primes.

9. The prime-ideal/irreducible-closed-set correspondence in [def-weil-pbc-krull-dimension-ring]
reverses inclusions: the closure of $\{\mathfrak q\}$ is $V(\mathfrak q)$, and it is a maximal
irreducible closed subset exactly when $\mathfrak q$ is minimal. By [def-sc-generic-point] these
are exactly the generic points of irreducible components of $\operatorname{Spec}T$. Hence steps
7–8 replace the last condition in step 4 by the generic-component condition of the statement.
Finally the fibrewise definition [def-trf-relative-assassin] identifies association of $z$ to
$\mathcal F_r$, respectively of $z'$ to $\mathcal F'_{r'}$, with membership in the two relative
assassins. This proves both implications of the desired equivalence. -/
theorem relativeAssassin_baseChange_iff {X S S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] (g : S' ⟶ S) (z' : ↑(Limits.pullback f g)) :
    z' ∈ relativeAssassin (Limits.pullback.snd f g)
        ((tensorPullback (Limits.pullback.fst f g)).obj F) ↔
      Limits.pullback.fst f g z' ∈ relativeAssassin f F ∧
        ∃ Z ∈ irreducibleComponents
            (Spec (Scheme.Pullback.Triplet.ofPoint ((pullbackSymmetry f g).hom z')).tensor),
          IsGenericPoint (Scheme.Pullback.SpecOfPoint ((pullbackSymmetry f g).hom z')) Z := by
  sorry

end AlgebraicGeometry.Scheme.Modules
