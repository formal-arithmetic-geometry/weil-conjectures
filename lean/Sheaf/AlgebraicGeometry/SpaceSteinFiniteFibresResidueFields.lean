/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
import Sheaf.AlgebraicGeometry.SpaceSteinFactorizationAffine
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceAtlasOpenRefinementPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Finite fibres and residue fields of the affine Stein factor of an algebraic space

Source: Stacks Project, More on Morphisms of Spaces, Tag 0E1C,
lemma-stein-universally-closed-residue-fields, specialized to a proper morphism;
Tag 0A19 supplies the canonical Stein projection
(blueprint: lem-sfb-space-stein-finite-fibres-residue-fields).

The ring is the compatible-section subring of the existing small affine etale model.
The projection is the spectrum of the existing canonical pullback `affineGlobalScalar`.
Finiteness of a residue-field ring map means finite dimension for its induced field algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a proper algebraic space over an arbitrary affine scheme, the canonical spectrum
of global functions has finite point fibres and finite residue extensions at every point
in each fibre. No Noetherian, flatness, reducedness or scheme-representability assumption
is made. The base `Spec (ULift ℤ)` is terminal and encodes absolute algebraic spaces.

Source: Stacks Project, More on Morphisms of Spaces, Tag 0E1C,
lemma-stein-universally-closed-residue-fields (proper case), using Tag 0A19
(blueprint: lem-sfb-space-stein-finite-fibres-residue-fields).

Proof:
1. Apply [lem-sfb-space-stein-factorization-affine] to the given proper $f$. Its evaluation map
   $q:X\to Z=\operatorname{Spec}B$ satisfies $f=\pi q$, its ring map $A\to B$ is integral, and
   every fibre over $\operatorname{Spec}\kappa(z)\to Z$ is nonempty. In particular $|q|$ is
   surjective: a field-valued point of this fibre represents a point of $X$ mapping to $z$. Only
   these clauses of the factorization node are used; geometric connectedness is not needed.
2. Fix $t\in T$, put $k=\kappa(t)$ and $C=\pi^{-1}(\{t\})\subseteq|Z|$. The points of $Z$ are
   primes of $B$, and $\pi$ sends a prime to its inverse image in $A$ [def-weil-affine-spectrum].
   By [lem-weil-pbc-integral-incomparability], distinct primes in $C$ cannot contain each other.
   In the Zariski topology a prime $\mathfrak q\,\!{}^\prime$ lies in $\overline{\{\mathfrak
   q\}}=V(\mathfrak q)$ exactly when $\mathfrak q\subseteq\mathfrak q\,\!{}^\prime$. Consequently
   $V(\mathfrak q)\cap C=\{\mathfrak q\}$ for every $\mathfrak q\in C$; in particular there are no
   distinct points of $C$ related by specialization.
3. Form $X_t=X\times_T\operatorname{Spec}k$, which is an algebraic space by [lem-trf-space-fibre-
   products-etale-covers]. Properness includes finite type [def-sfb-space-morphism-properties].
   Base-change stability in [lem-sfb-stack-finite-type-calculus], whose statement explicitly
   agrees with the ordinary algebraic-space notion, makes $X_t\to\operatorname{Spec}k$ finite
   type. Its quasi-compactness, tested on the quasi-compact scheme $\operatorname{Spec}k$, says
   that $X_t$ admits a surjective etale map from a quasi-compact scheme; by the last clause of
   [lem-a1-space-finite-affine-subatlas] its point space $|X_t|$ is quasi-compact. The map $X_t\to
   X\xrightarrow q Z$ has image exactly $C$: one inclusion follows from $f=\pi q$; for the other,
   choose $x\in|X|$ mapping to $z\in C$ by step 1, and apply the point-fibre-product surjectivity
   of [lem-a1-space-point-open-calculus] to $X\to T\leftarrow\operatorname{Spec}k$. It supplies a
   point of $X_t$ projecting to $x$, hence mapping to $z$. Every point map used here is continuous
   by the same node.
4. Choose a scheme atlas of $X_t$ as in [def-trf-algebraic-space]. Refine it to a disjoint union
   of affine schemes by [lem-a1-space-atlas-open-refinement-pullback]. Apply [lem-a1-space-finite-
   affine-subatlas] to the quasi-compact point space from step 3. This gives finitely many affine
   schemes $U_j=\operatorname{Spec}R_j$ whose coproduct maps to $X_t$ by a representable
   surjective etale map; by [lem-a1-space-point-open-calculus] this map is surjective on points,
   so the maps $|U_j|\to|X_t|$ are jointly surjective. Composing with $X_t\to Z$ gives scheme
   morphisms $h_j:U_j\to Z$, since a map between representable sheaves is the corresponding scheme
   map. Their point images cover $C$, by step 3. The chart test of [def-sfb-space-morphism-
   properties], with target chart the identity of $\operatorname{Spec}k$, makes each
   $U_j\to\operatorname{Spec}k$ locally of finite type.
5. By [lem-weil-pbc-lft-affine-pairs], $R_j$ is a finitely generated $k$-algebra. The field $k$ is
   Noetherian: a nonzero ideal contains an invertible element and hence $1$, so its only ideals
   are $(0)$ and $(1)$. Therefore [lem-weil-pbc-finite-type-algebra-noetherian] makes $R_j$
   Noetherian. The single affine open $U_j$ satisfies [pqf-def-locnoeth], and $U_j$ is quasi-
   compact by [lem-weil-pbc-affine-scheme-qcqs]; thus it is a Noetherian scheme. Applying [lem-sc-
   noetherian-closed-subset-finite-components] to the closed subset $E=U_j$ writes $U_j$ as a
   finite union of irreducible components. By [lem-sc-scheme-sober] each nonempty component has a
   generic point $\eta_{j,a}$. There are only finitely many such generic points over all $j$, and
   every $u\in U_j$ lies in $\overline{\{\eta_{j,a}\}}$ for at least one $a$.
6. For $z\in C$, choose $j$ and $u\in U_j$ with $h_j(u)=z$ (step 4), then choose $\eta_{j,a}$
   specializing to $u$ (step 5). Continuity of the scheme map $h_j$ gives
   $h_j(u)\in\overline{\{h_j(\eta_{j,a})\}}$. Both points belong to $C$, so step 2 forces
   $z=h_j(\eta_{j,a})$. Thus $C$ is contained in the image of the finite set of generic points
   from step 5. The reverse containment follows because each chart maps into $C$. Hence $C$ is
   finite. This supplies the topological argument omitted in Tag 0E1C: it uses generic points of
   the scheme charts and never assumes that an arbitrary Noetherian topological space is sober.
7. Now fix $z\in C$ and choose a chart $h_j$ whose image contains $z$. Write $\mathfrak q_z$ for
   the prime of $B$ corresponding to $z$. The subset $E_j=h_j^{-1}(V(\mathfrak q_z))$ is closed in
   $U_j$, and by step 2 and $h_j(U_j)\subseteq C$ it equals $h_j^{-1}(\{z\})$; it is nonempty. By
   [lem-sfb-finite-type-points-detect-open], choose a finite type point $u\in E_j$, meaning that
   $\operatorname{Spec}\kappa(u)\to U_j$ is of finite type. Composing it with the locally finite
   type scheme map $U_j\to\operatorname{Spec}k$ is locally of finite type by clause (e) of [lem-
   weil-pbc-proper-fp-permanence]. Apply [lem-sfb-finite-type-field-point-characterization] to
   this composite. Since the target is the one-point scheme $\operatorname{Spec}k$, it gives
   $[\kappa(u):k]<\infty$. This uses a finite type point in a closed subset of an actual scheme
   chart, so no assumption about closed rational points or representability of $X$ is made.
8. The scheme morphism $h_j$ induces an embedding $\kappa(z)\hookrightarrow\kappa(u)$ on residue
   fields [def-weil-residue-field]. It is an embedding over $k=\kappa(t)$: the maps $U_j\to Z\to
   T$ and $U_j\to\operatorname{Spec}k\to T$ agree, so their local-ring maps and residue maps
   agree; the latter factors through the canonical residue map at $t$. Regard $\kappa(z)$ as a
   $k$-linear subspace of $\kappa(u)$. Any $k$-linearly independent family in it remains
   independent under the injection, hence has size at most $\dim_k\kappa(u)$, which is finite by
   step 7. Therefore $[\kappa(z):\kappa(t)]<\infty$. If $C$ is empty there is no $z$ to treat; if
   $X$ is empty the atlas and the finite sets above can all be empty. The argument only used
   Noetherianity of finite type algebras over $k$, and imposed no Noetherian, reducedness,
   flatness or finite-presentation hypothesis on the original base or morphism. -/
theorem steinAffineProjection_finite_fibres_residueFields (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))))
    (hf : MapIsProper f) (t : Spec (.of A)) :
    ((Spec.map (@CommRingCat.ofHom A (RingCat.sectionsSubring X.smallStructureRings.obj)
      inferInstance
      (@Subring.toCommRing (∀ T : X.SmallEtaleModelᵒᵖ, X.smallStructureSheaf.obj.obj T)
        inferInstance (RingCat.sectionsSubring X.smallStructureRings.obj))
      (affineGlobalScalar A
        (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) (Iso.refl _) X f))) ⁻¹' {t}).Finite ∧
      ∀ z : Spec (@CommRingCat.of (RingCat.sectionsSubring X.smallStructureRings.obj)
        (@Subring.toCommRing (∀ T : X.SmallEtaleModelᵒᵖ, X.smallStructureSheaf.obj.obj T)
          inferInstance (RingCat.sectionsSubring X.smallStructureRings.obj))),
        (Spec.map (@CommRingCat.ofHom A (RingCat.sectionsSubring X.smallStructureRings.obj)
          inferInstance
          (@Subring.toCommRing (∀ T : X.SmallEtaleModelᵒᵖ, X.smallStructureSheaf.obj.obj T)
            inferInstance (RingCat.sectionsSubring X.smallStructureRings.obj))
          (affineGlobalScalar A
            (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) (Iso.refl _) X f))) z = t →
          (Scheme.Hom.residueFieldMap
            (Spec.map (@CommRingCat.ofHom A (RingCat.sectionsSubring X.smallStructureRings.obj)
            inferInstance
            (@Subring.toCommRing (∀ T : X.SmallEtaleModelᵒᵖ, X.smallStructureSheaf.obj.obj T)
              inferInstance (RingCat.sectionsSubring X.smallStructureRings.obj))
            (affineGlobalScalar A
              (Over.mk (specULiftZIsTerminal.from (Spec (.of A))))
              (Iso.refl _) X f))) z).hom.Finite := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
