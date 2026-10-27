module

public import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAtlasTestOpenSubsets
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.Topology.GlueSheavesOfModules

/-! # Torsion-controlled algebraization on a Noetherian algebraic space

Source: Stacks Project, spaces-more-morphisms.tex, Tag 08BB (lemma-existence-easy)
(blueprint: lem-sfb-space-easy-torsion-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A map into a coherent completion with uniformly torsion kernel and cokernel
algebraizes to a unique torsion-controlled coherent triple. Uniqueness includes both
the algebraic map and the specified completion isomorphism.

Source: Stacks Project, Tag 08BB (lemma-existence-easy)
(blueprint: lem-sfb-space-easy-torsion-algebraization).

Proof:
1. Choose an etale scheme atlas $V\to X$ and cover $V$ by affine opens. Each affine is
Noetherian, by the locally Noetherian chart condition. Their images in $|X|$ are open: the
atlas-test lemma makes their inverse images in $V$ open, and the final-topology definition then
applies. They cover $|X|$, so quasi-compactness gives finitely many, with scheme coproduct $U$.
Its components are open and closed by the scheme-coproduct theorem; the induced map is etale
since it is etale on these open components. Thus $p:U\to X$ is a surjective etale atlas with $U$
a Noetherian scheme. A finite disjoint union of Noetherian affine schemes is Noetherian since
its components are open and closed. The empty space is handled by the empty atlas. This uses no
separation or field hypothesis.
Uses: def-trf-algebraic-space, def-sfb-space-coherent-adic-system, def-a1-space-point-topology,
lem-a1-space-atlas-test-open-subsets, lem-weil-pbc-scheme-coproduct-family.

2. Etale pullback here is restriction on localized sites. Hence it preserves the ordinary sheaf
kernels and cokernels and the ideal-action maps. In particular $p^*u$ has its component kernels
and cokernels killed by $(p^*L)^t$. The scheme Zariski/etale equivalence is exact, preserves
finite presentation and commutes naturally with tensor pullback. Products $L^nM$ are images of
the multiplication maps $L^{\otimes n}\otimes M\to M$; exactness and the tensor comparison
therefore identify these products and their quotients on both sites. Consequently the
equivalence identifies completion diagrams, their transition maps, and the component
annihilation hypothesis, not merely the individual underlying modules. On the Noetherian scheme
$U$, coherence is the finite-presentation condition tested on affine charts. Apply the scheme
torsion-triple theorem to the resulting Zariski data. Return to the etale site to obtain
$(E_U,b_U,\gamma_U)$ and $s\ge1$ killing the actual kernel and cokernel of $b_U$. This theorem
also gives uniqueness among triples having that actual torsion condition.
Uses: def-trf-algebraic-space, def-sfb-space-coherent-adic-system, lem-trf-scheme-zariski-etale-
quasi-coherent-equivalence, lem-sfb-scheme-etale-module-exact-finiteness-comparison, lem-sfb-
space-qcoh-affine-chart-calculus, lem-weil-pbc-easy-algebraization-torsion-triple.

3. Put $R=U\times_XU$, with projections $r_1,r_2$. It is a scheme, etale over $U$, by the
representable diagonal and etale scheme-test lemma. It is locally Noetherian by the chart
convention; we do not assume $R$ affine or globally Noetherian. On each affine open $W\subset
R$, the restrictions of $r_1^*(E_U,b_U,\gamma_U)$ and $r_2^*(E_U,b_U,\gamma_U)$ are two torsion-
controlled triples for the same restricted $u$. The site comparisons from step 2 preserve these
data. The scheme theorem gives the unique isomorphism $a_W:r_1^*E_U|_W\to r_2^*E_U|_W$
preserving $b$ and $\gamma$. On an intersection of two such opens, pass to any affine open
inside the intersection; scheme uniqueness makes the two maps equal there. Glue the Zariski
maps, and their inverses, by the gluing-morphisms theorem; the site equivalence gives $a$ on
$R$. The resulting map is an isomorphism since its composites with the glued inverse are
identities on the affine cover. All the required equations hold there and therefore globally.
Uses: lem-trf-space-representable-etale-scheme-tests, def-sfb-space-coherent-adic-system, lem-
weil-pbc-easy-algebraization-torsion-triple, lem-weil-pbc-glue-sheaves-of-modules, lem-trf-
scheme-zariski-etale-quasi-coherent-equivalence.

4. On the triple fibre product the two arrows $a_{23}a_{12}$ and $a_{13}$ preserve $b$ and
$\gamma$: for the formal comparisons their composites are respectively
$\gamma_3\gamma_2^{-1}\gamma_2\gamma_1^{-1}$ and $\gamma_3\gamma_1^{-1}$. On every affine open,
scheme uniqueness identifies the arrows. The gluing-morphisms theorem identifies them globally.
On the diagonal the same uniqueness identifies $a$ with the identity. Thus $(E_U,a)$ is a
groupoid-module descent datum. The quasi-coherent groupoid equivalence descends it to a coherent
$E$ on $X$, since $E_U$ is coherent, and descends $b_U$ to $b:E\to H$. For each $n$, the chart
calculus identifies the pullback of $E/L^nE$ with $E_U/(p^*L)^nE_U$. The component
$\gamma_{U,n}$ commutes with the descent data because $a$ preserves $\gamma_U$; full
faithfulness descends it and its inverse to $\gamma_n:P_n\simeq E/L^nE$. Transition
compatibility is an equality of module maps checked on $U$ by faithfulness. The same argument
descends $u_n=\widehat b_n\gamma_n$. Hence the $\gamma_n$ form the required system isomorphism
$\gamma$.
Uses: lem-weil-pbc-easy-algebraization-torsion-triple, lem-weil-pbc-glue-sheaves-of-modules,
lem-sfb-space-qcoh-groupoid-equivalence, lem-sfb-space-qcoh-affine-chart-calculus.

5. The kernel and cokernel of $b$ are quasi-coherent and their restrictions to $U$ are the
actual kernel and cokernel of $b_U$, by the affine-chart calculus. Their multiplication maps by
$L^s$ restrict to zero, since step 2 supplied the single exponent $s$ on the whole Noetherian
scheme $U$. The faithful groupoid restriction functor therefore makes these multiplication maps
zero on $X$. This proves the required global bound on the ordinary sheaf kernel and cokernel of
$b$; no assertion that completion is faithful has been used.
Uses: lem-sfb-space-qcoh-affine-chart-calculus, lem-sfb-space-qcoh-groupoid-equivalence.

6. Given any two triples on $X$, their restrictions to $U$ satisfy the scheme theorem, including
the actual torsion condition on each algebraic map. It gives a unique $v_U:E_U\simeq E'_U$ with
$b'_Uv_U=b_U$ and $\widehat v_U\gamma_U=\gamma'_U$. On $R$, the two descent comparisons of $v_U$
are isomorphisms between the same triples. On every affine open of $R$ they agree by scheme
uniqueness; gluing-morphisms uniqueness makes them equal on $R$. Thus $v_U$ respects the
groupoid data and descends to an isomorphism $v$. Its two equations can be checked after
restriction to $U$, componentwise for the completion equation, and hold by full faithfulness.
Any other such $v$ restricts to $v_U$ by scheme uniqueness and equals $v$ by faithfulness. This
proves the stated uniqueness for any two triples.
Uses: lem-weil-pbc-easy-algebraization-torsion-triple, lem-weil-pbc-glue-sheaves-of-modules,
lem-sfb-space-qcoh-groupoid-equivalence.
-/
theorem exists_unique_torsionControlled_algebraization
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (L : QuasiCoherentIdeal X)
    (H : ObjectProperty.FullSubcategory (C := X.Modules)
      (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj M)))
    (P : CoherentAdicSystem X L hln hqc hqs)
    (u : P ⟶ (coherentAdicCompletion L hln hqc hqs).obj H)
    (htorsion : CoherentAdicKernelCokernelKilled L u.hom) :
    ∃ (E : ObjectProperty.FullSubcategory (C := X.Modules)
        (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
          RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
            ((X.schemeRestriction T).obj M)))
      (b : E ⟶ H) (γ : P ≅ (coherentAdicCompletion L hln hqc hqs).obj E),
      u = γ.hom ≫ (coherentAdicCompletion L hln hqc hqs).map b ∧
      (∃ s : ℕ, 1 ≤ s ∧
        (∀ k : KernelFork b.hom, IsLimit k → AdicPowerKills L s k.pt) ∧
        (∀ c : CokernelCofork b.hom, IsColimit c → AdicPowerKills L s c.pt)) ∧
      ∀ (E' : ObjectProperty.FullSubcategory (C := X.Modules)
          (fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
            RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
              ((X.schemeRestriction T).obj M)))
        (b' : E' ⟶ H) (γ' : P ≅ (coherentAdicCompletion L hln hqc hqs).obj E'),
        u = γ'.hom ≫ (coherentAdicCompletion L hln hqc hqs).map b' →
        (∃ s : ℕ, 1 ≤ s ∧
          (∀ k : KernelFork b'.hom, IsLimit k → AdicPowerKills L s k.pt) ∧
          (∀ c : CokernelCofork b'.hom, IsColimit c → AdicPowerKills L s c.pt)) →
        ∃! v : E ≅ E', v.hom ≫ b' = b ∧
          γ.hom ≫ (coherentAdicCompletion L hln hqc hqs).map v.hom = γ'.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
