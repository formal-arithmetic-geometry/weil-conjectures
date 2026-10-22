module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sober
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Good components of a semilinear Sylow quotient

Source: ILO, Travaux de Gabber, Expose X, 2.3, Step 2, diagram (2.c), printed p. 151
(blueprint: lem-sfb-semilinear-sylow-good-components).

The subgroup quotients are given geometric categorical quotients, not quotients whose
existence must be proved. The maps `d` are the unique descents of `h`. The field `F` is
identified with the fixed field by `hF`. Inverse pullback on constants matches the left
scheme action with the left action by field automorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Select clopen components with prime-to-ell residue degree over every generic point.
Source: ILO X 2.3, Step 2, diagram (2.c), printed p. 151
(blueprint: lem-sfb-semilinear-sylow-good-components).

Proof (the live DAG's thirteen steps; theorems are postponed in stage 2):
1. Put $E=K^G$, $H=\operatorname{im}(G\to\operatorname{Aut}_eK)$ and
   $J=\operatorname{im}(L\to\operatorname{Aut}_eK)$. These image groups act faithfully. The
   finite-field-action theorem gives $[K:E]=|H|$ and $[K:F]=|J|$, and makes $K/F$ finite Galois.
   Its automorphism group has order $[K:F]=|J|$ by the finite-Galois theorem, so the inclusion of
   $J$ into that group is equality. This proves the asserted Galois-group clause without assuming
   the original action of $L$ faithful.
   Uses: lem-wf-finite-field-action-fixed-degree, lem-weil-pbc-finite-galois-fixed-field.
2. Let $N=\ker(G\to H)$. Counting cosets gives $[G:L]=[H:J][N:N\cap L]$: the map $G/L\to H/J$ is
   onto and each fibre has cardinal $[N:N\cap L]$. Thus $[H:J]$ is prime to $\ell$. The degree
   tower $E\subseteq F\subseteq K$ gives $[F:E]=|H|/|J|=[H:J]$. In positive characteristic $p$,
   the finite purely inseparable extension $E/e$ is normal (each minimal polynomial has only its
   one root), and has exactly one embedding into an algebraic closure; the normal-field-degree-
   factors theorem therefore makes $[E:e]$ a power of $p$. In characteristic zero $E=e$ by the
   meaning of purely inseparable. As $p\ne\ell$, the second degree tower gives $[F:e]=[F:E][E:e]$
   prime to $\ell$. All towers are finite since their fields lie in the given finite extension
   $K/e$.
   Uses: lem-weil-pbc-field-degree-multiplicativity, lem-exc-normal-field-degree-factors.
3. Smoothness over $K$ makes $Y$ regular and locally Noetherian, hence normal. Projectivity makes
   $Y/K$ proper, hence finite type; since a field is Noetherian, the finite-type theorem makes
   $Y$ Noetherian. The normal-component theorem decomposes $Y$ as a finite disjoint union of
   open-and-closed normal integral components. This applies even when the components are not
   geometrically integral.
   Uses: lem-weil-pbc-smooth-scheme-over-field-regular, rem-pc-regular-normal, lem-kun-
   projective-implies-proper, lem-weil-pbc-finite-type-over-noetherian.
4. For $k=e$ and for $k=F$, the morphism $\operatorname{Spec}K\to\operatorname{Spec}k$ is finite
   because $K/k$ is finite-dimensional. The finite-projective-bundle theorem followed by the
   ample-base conversion makes it H-projective: the trivial line on $\operatorname{Spec}k$ is
   ample, since its unit section has the whole affine scheme as nonvanishing locus. Compose with
   the given H-projective $Y/K$ to obtain $Y/k$ H-projective, hence proper. The invariant map
   $Y\to\operatorname{Spec}F$ descends by the categorical property of $q_L$, and gives $Q$ its
   $F$-structure; the descended map agrees with the original $e$-structure. Likewise the
   $G$-invariant structure map $Y\to\operatorname{Spec}e$ descends through $q_G$ and gives
   $Z=Y/G$ its $e$-structure, so $q_G$ is a morphism of $e$-schemes and $q_L$ a morphism of
   $F$-schemes; uniqueness in the categorical property shows that an invariant $e$- (resp.
   $F$-)morphism factors through a morphism of $e$- (resp. $F$-)schemes. Apply the normal-proper-
   quotient lemma to $(Y,G,e)$ and $(Y,L,F)$. Thus $Z=Y/G$ is normal proper finite type over $e$,
   and $Q=Y/L$ is normal proper finite type over $F$; both are Noetherian.
   Uses: def-weil-finite-integral-morphism, def-weil-pbc-ample-invertible-module, lem-trf-finite-
   projective-bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-
   composition, lem-kun-projective-implies-proper, lem-sfb-finite-quotient-normal-proper.
5. Decompose $Q$ into its finitely many clopen normal integral components $C$. For each $C$, its
   inverse image $X_C=q_L^{-1}C$ is clopen in $Y$. A clopen subscheme is also a closed subscheme,
   as the defining ideal is zero on it and the unit ideal on its complement. Compose this closed
   inclusion with a projective embedding of $Y/F$ to obtain a projective embedding of $X_C/F$,
   and hence an ample invertible sheaf on $X_C$. The restricted map $X_C\to C$ is finite
   surjective: on an affine open of $C$ it is the same finite algebra as for $q_L$. Apply finite-
   normal ample descent to obtain an ample invertible sheaf on $C$. Glue these sheaves on the
   disjoint components to an invertible sheaf on $Q$. It is ample: extend an affine-nonvanishing
   section on a chosen component by zero on all other components; its nonvanishing locus is the
   original affine open. Quasi-compactness holds because there are finitely many components. This
   uses the definition of ample, without descending a chosen linearization.
   Uses: rem-pc-regular-normal, lem-weil-pbc-closed-immersion-comp, lem-weil-pbc-projective-
   ample-invertible, def-weil-finite-integral-morphism, lem-sfb-finite-normal-ample-descent, def-
   weil-pbc-ample-invertible-module.
6. The ample-immersion theorem, applicable since $Q/F$ is finite type, gives an immersion
   $Q\to\mathbf P^n_F$. The target is separated over $F$ and $Q$ is proper over $F$, so the
   proper-to-separated-target theorem makes the immersion proper. A proper immersion is closed.
   Thus $Q$ is projective over $F$ in the required finite-projective-space convention.
   Uses: lem-weil-pbc-ample-very-ample-immersion-affine-base, lem-weil-pbc-projective-space-proj-
   separated, lemma-nagata-proper-to-separated-target, lem-weil-pbc-proper-immersion-closed, def-
   kun-projective.
7. Fix a generic point $b$ of $B$. It lies in the specified dense open $U$. The finite universal
   homeomorphism $Z_U\to U$ has exactly one point $t$ over $b$, which is generic: on the
   component containing $b$ it is a homeomorphism. Its residue extension $T=\kappa(t)/\kappa(b)$
   is finite by finiteness of this morphism and purely inseparable because a universal
   homeomorphism is universally injective, hence radicial. The generic-field comparison for
   $q_G:Y\to Z$ identifies the components above $t$ as one $G$-orbit. Choose a generic point
   $\eta$ in this orbit, put $M=\kappa(\eta)$ and $D=\operatorname{Stab}_G(\eta)$. The same
   comparison gives $T=M^D$ with its canonical embedding in $M$. All components of $Z$ meet
   $Z_U$: every generic of $Y$ maps to a generic of $B$ by hypothesis, and the quotient
   comparison maps these onto the generic points of $Z$.
   Uses: def-weil-universal-homeomorphism, def-weil-radicial-morphism, def-weil-finite-integral-
   morphism, lem-sfb-finite-quotient-generic-fields.
8. Choose an $\ell$-Sylow subgroup $P$ of the finite stabilizer $D$. Regard $P$ as an
   $\ell$-subgroup of $G$ and apply Sylow conjugate containment to obtain $g$ with
   $gPg^{-1}\subseteq L$. Replace $\eta$ by $\eta'=g\eta$, and write $D'=gDg^{-1}$ and
   $M'=\kappa(\eta')$. Put $S=D'\cap L$. It contains the $\ell$-Sylow subgroup $gPg^{-1}$ of
   $D'$, while it is itself an $\ell$-group as a subgroup of $L$. Hence $|S|=|P|$ and $[D':S]$ is
   prime to $\ell$. The point $\eta'$ still maps to $b$ because $h$ is invariant. This chooses a
   conjugate separately for this generic point of $B$, rather than imposing a simultaneous
   containment on all stabilizers.
   Uses: lem-weil-pbc-sylow-subgroup-prime-index, lem-sfb-sylow-conjugate-containment.
9. Let $c=q_L(\eta')$, a generic point of $Q$. The quotient comparison gives $\kappa(c)=(M')^S$
   and $T=(M')^{D'}$. Let $A$ and $A_0$ be the images of $D'$ and $S$ in
   $\operatorname{Aut}(M')$. The faithful finite-action theorem gives $[M':T]=|A|$ and
   $[M':\kappa(c)]=|A_0|$. The tower law gives $[\kappa(c):T]=[A:A_0]$. Counting fibres of
   $D'/S\to A/A_0$ shows that this index divides $[D':S]$, so it is prime to $\ell$. Since
   $T/\kappa(b)$ is finite purely inseparable, its degree is a characteristic power (or one in
   characteristic zero), by the normal-field-degree-factors theorem as in step 2. Multiplying
   degrees now proves that $[\kappa(c):\kappa(b)]$ is finite and prime to $\ell$. The field-
   action theorem is applied to image groups, so generic inertia is allowed.
   Uses: lem-sfb-finite-quotient-generic-fields, lem-wf-finite-field-action-fixed-degree, lem-
   weil-pbc-field-degree-multiplicativity, lem-exc-normal-field-degree-factors.
10. Do this for each of the finitely many generic points $b$ of $B$, choosing one resulting
   component of $Q$ over each. Let $Q^\circ$ be the union of those components. By the normal-
   component theorem it is open and closed, normal, and its generic points are precisely the
   finitely many selected generic points; each has the finite prime-to-$\ell$ residue degree
   proved in step 9. It meets every generic fibre of $B$. Its closed inclusion into the
   projective $F$-scheme $Q$, composed with the projective embedding of $Q$, makes $Q^\circ/F$
   projective. No condition is inferred for any component omitted from this union.
   Uses: rem-pc-regular-normal, lem-weil-pbc-closed-immersion-comp, def-kun-projective.
11. The finite map $\operatorname{Spec}F\to\operatorname{Spec}e$ is H-projective by the finite-
   projective-bundle theorem and the ample-base conversion, again using the unit section of the
   trivial line on the affine base. Composition therefore gives a closed immersion
   $i:Q^\circ\hookrightarrow\mathbf P^N_e$. Let $d:Q^\circ\to B$ be the descended map, restricted
   to this union. The diagonal of $B/e$ is closed because $B/e$ is proper. Its base change is the
   graph $Q^\circ\to Q^\circ\times_eB$, so the graph is closed. The map
   $Q^\circ\times_eB\to\mathbf P^N_e\times_eB$ is the base change of $i$, hence closed. Their
   composite is a closed immersion over $B$, exhibiting $d$ as H-projective, and thus also
   projective in the projective-bundle convention (the ambient bundle is that of $\mathcal
   O_B^{N+1}$).
   Uses: def-weil-finite-integral-morphism, def-weil-pbc-ample-invertible-module, lem-trf-finite-
   projective-bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-
   composition, def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change, lem-weil-
   pbc-closed-immersion-comp, def-kun-projective, def-trf-projective-bundle-morphism.
12. Projectivity makes $d$ proper, so its image is closed by the definition of universally closed
   applied to the identity base change. This image contains every generic point of $B$ by
   construction. A closed subset containing the generic point of every irreducible component
   contains every component, so the image is all of $B$. Thus $d$ is surjective. The generic-
   point and residue-degree clauses were established for every component retained in $Q^\circ$,
   not just for their total degree.
   Uses: lem-kun-projective-implies-proper, def-weil-proper-morphism.
13. Set $Y^\circ=q_L^{-1}(Q^\circ)$. It is clopen and $L$-stable. The restricted quotient is
   finite and surjective, has the same orbit geometric fibres, and has invariant structure sheaf
   by restricting the corresponding statements for $q_L$ to the open $Q^\circ$; on each affine
   open the same finite algebra occurs. Its categorical property can be checked directly. Given
   an invariant morphism $f:Y^\circ\to T$, extend it on the disjoint complement by $q_L$ to
   obtain an invariant map $Y\to T\amalg(Q\setminus Q^\circ)$. Descend it through $q_L$, then
   restrict to $Q^\circ$: surjectivity on points forces this restriction to land in the summand
   $T$. This gives the required factorization; uniqueness follows either from the categorical
   uniqueness for the extended map or from that same descent construction. Hence $Y^\circ\to
   Q^\circ$ is the finite quotient by $L$ claimed in the statement.
   Uses: def-weil-finite-integral-morphism, def-weil-open-immersion.
-/
theorem semilinear_sylow_good_components
    (e K : Type u) [Field e] [Field K] [Algebra e K] [Module.Finite e K]
    (ell : ℕ) (hell : ell.Prime) (hchar : ell ≠ ringChar e)
    (G : Type v) [Group G] [Finite G] (ρ : G →* (K ≃ₐ[e] K))
    (hfixed : IsPurelyInseparable e (IntermediateField.fixedField ρ.range))
    (B Y : Scheme.{u}) (b : B ⟶ Spec (.of e)) (p : Y ⟶ Spec (.of K))
    [Nonempty B] [IsProper b]
    (hBnormal : ∀ x : B, IsDomain (B.presheaf.stalk x) ∧
      IsIntegrallyClosed (B.presheaf.stalk x))
    (hBcomponents : ∃ (n : ℕ) (V : Fin n → B.Opens),
      (∀ i, IsIntegral (V i).toScheme) ∧ Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      (⨆ i, V i) = ⊤)
    [Smooth p] [IsHProjective p] (a : G →* Aut Y)
    (hequivariant : ∀ g : G, (a g).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom))
    (h : Y ⟶ B) (hbase : h ≫ b = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)))
    (hinvariant : ∀ g : G, (a g).hom ≫ h = h)
    (hhprojective : IsProjectiveBundle h) (hhsurjective : Surjective h)
    (hhgeneric : ∀ y ∈ genericPoints Y,
      h y ∈ genericPoints B ∧ (h.residueFieldMap y).hom.Finite)
    (Q : Subgroup G → Scheme.{u}) (q : ∀ H : Subgroup G, Y ⟶ Q H)
    (hquot : ∀ H : Subgroup G,
      IsAdmissibleFiniteSchemeQuotient (a.comp H.subtype) (q H))
    (hcat : ∀ (H : Subgroup G) (T : Scheme.{u}) (f : Y ⟶ T),
      (∀ g : H, (a g).hom ≫ f = f) → ∃! r : Q H ⟶ T, q H ≫ r = f)
    (hgeom : ∀ (H : Subgroup G) (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Surjective (fun t : Spec (.of Ω) ⟶ Y ↦ t ≫ q H) ∧
      ∀ t₁ t₂ : Spec (.of Ω) ⟶ Y, t₁ ≫ q H = t₂ ≫ q H ↔
        ∃ g : H, t₁ ≫ (a g).hom = t₂)
    (d : ∀ H : Subgroup G, Q H ⟶ B) (hd : ∀ H, q H ≫ d H = h)
    (hdense : ∃ V : B.Opens, Dense (V : Set B) ∧
      (∀ x ∈ genericPoints B, x ∈ V) ∧
      IsFinite ((d ⊤).resLE V ((d ⊤) ⁻¹ᵁ V) le_rfl) ∧
      (topologically IsHomeomorph).universally
        ((d ⊤).resLE V ((d ⊤) ⁻¹ᵁ V) le_rfl))
    (L : Subgroup G) (hLorder : ∃ n : ℕ, Nat.card L = ell ^ n)
    (hLindex : Nat.Coprime L.index ell)
    (F : IntermediateField e K) (hF : F = IntermediateField.fixedField (L.map ρ)) :
    Module.Finite e F ∧ Nat.Coprime (Module.finrank e F) ell ∧
    Module.Finite F K ∧ IsGalois F K ∧ F.fixingSubgroup = L.map ρ ∧
    ∃ (sF : Q L ⟶ Spec (.of F)),
      q L ≫ sF = p ≫ Spec.map (CommRingCat.ofHom F.subtype) ∧
      ∃ U : (Q L).Opens, IsClosed (U : Set (Q L)) ∧
        (∃ C : Set (Set (Q L)), C ⊆ irreducibleComponents (Q L) ∧ (U : Set (Q L)) = ⋃₀ C) ∧
        (∀ x ∈ genericPoints B, ∃ z : U.toScheme, (U.ι ≫ d L) z = x) ∧
        (∀ z : U.toScheme, IsDomain (U.toScheme.presheaf.stalk z) ∧
          IsIntegrallyClosed (U.toScheme.presheaf.stalk z)) ∧
        IsHProjective (U.ι ≫ sF) ∧ IsProjectiveBundle (U.ι ≫ d L) ∧
        Surjective (U.ι ≫ d L) ∧
        (∀ z ∈ genericPoints U.toScheme, (U.ι ≫ d L) z ∈ genericPoints B ∧
          ((U.ι ≫ d L).residueFieldMap z).hom.Finite ∧
          Nat.Coprime ((U.ι ≫ d L).residueDegree z) ell) ∧
        IsClosed ((q L ⁻¹ᵁ U) : Set Y) ∧
        ∃ aU : L →* Aut (q L ⁻¹ᵁ U).toScheme,
          (∀ g : L, (aU g).hom ≫ (q L ⁻¹ᵁ U).ι =
            (q L ⁻¹ᵁ U).ι ≫ (a g).hom) ∧
          IsAdmissibleFiniteSchemeQuotient aU
            ((q L).resLE U (q L ⁻¹ᵁ U) le_rfl) ∧
          (∀ (T : Scheme.{u}) (f : (q L ⁻¹ᵁ U).toScheme ⟶ T),
            (∀ g : L, (aU g).hom ≫ f = f) →
              ∃! r : U.toScheme ⟶ T, (q L).resLE U (q L ⁻¹ᵁ U) le_rfl ≫ r = f) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
            Function.Surjective (fun t : Spec (.of Ω) ⟶ (q L ⁻¹ᵁ U).toScheme ↦
              t ≫ (q L).resLE U (q L ⁻¹ᵁ U) le_rfl) ∧
            ∀ t₁ t₂ : Spec (.of Ω) ⟶ (q L ⁻¹ᵁ U).toScheme,
              t₁ ≫ (q L).resLE U (q L ⁻¹ᵁ U) le_rfl =
                  t₂ ≫ (q L).resLE U (q L ⁻¹ᵁ U) le_rfl ↔
                ∃ g : L, t₁ ≫ (aU g).hom = t₂ := by
  sorry

end AlgebraicGeometry
