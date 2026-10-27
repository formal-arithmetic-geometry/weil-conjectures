/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.PointedAffineDevissage
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import Sheaf.FieldTheory.PurelyTranscendentalExtension
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Elementary étale refinement of a pointed affine dévissage

Source: Stacks Project, flat.tex, Tag 05HE, lemma-elementary-etale-neighbourhood;
Tag 05HR, proposition-existence-complete-at-x, for the generic basis and cokernel.
The auxiliary datum omits support-dimension equalities.
(blueprint: lem-trf-devissage-pointed-etale-refinement).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Refine the target and base of a pointed affine one-step datum, retaining its
presentation, dimension, generic basis maps and their cokernels. The open immersion `j`
identifies the new affine target with an affine open of the indicated fibre product.
`finiteSquare` identifies the new finite source with `Z ×[Y] Y''`, without choosing a
particular model of that fibre product. Both module isomorphisms are pinned by their
canonical base-change maps; the final quotient square pins the cokernel identification.

Source: Stacks Project, flat.tex, Tags 05HE and 05HR
(blueprint: lem-trf-devissage-pointed-etale-refinement).

Proof:
1. Choose an affine open $A\subset B'$ containing $b'$, then an affine open $U\subset
   Y'\times_{B'}A$ containing $y'$, using [lem-weil-pbc-affine-opens-basis]. The composite $U\to
   Y$ is etale by [lem-weil-pbc-etale-composition-cancellation], and elementary at $y'$ because
   open immersions preserve residue fields [lem-weil-pbc-residue-field-point-naturality]. The map
   $U\to Y\times_B A$ is etale: its composite to $Y$ and the projection to $Y$ are etale, the
   latter by [lem-weil-pbc-etale-scheme-base-change], so apply cancellation. First, $Y\to B$ is
   smooth of relative dimension $d$ in the sense of [def-sbc-smooth-morphisms]: it is locally of
   finite presentation between affine schemes, hence of finite presentation and so of finite type
   by [lem-weil-pbc-qcqs-morphism-permanence] and [lem-weil-pbc-affine-scheme-qcqs], so each fibre
   $Y_t$ is of finite type over $\kappa(t)$ by [lem-sfb-finite-type-composition-base-change]; it
   is irreducible of dimension $d$ by [def-trf-pointed-scheme-devissage-data], so
   $\dim_{y_1}Y_t=\dim Y_t=d$ at every $y_1\in Y_t$ by [lem-sc-dimension-locally-algebraic]. Hence
   $U\to A$ is smooth of relative dimension $d$ by [lem-sbc-smooth-relative-dimension-permanence].
   It is locally of finite presentation by [def-sbc-smooth-morphisms], and of finite presentation
   by [lem-weil-pbc-qcqs-morphism-permanence] and [lem-weil-pbc-affine-scheme-qcqs], since source
   and target are affine.
2. Put $k=\kappa(b')=\kappa(b)$. The marked residue field of $U$ is $\kappa(y')=\kappa(y)$,
   compatibly over $k$. This extension is purely transcendental by [def-trf-pointed-scheme-
   devissage-data]. Its transcendence basis is finite: $U_{b'}$ is of finite type over $k$ by
   [lem-sfb-finite-type-composition-base-change] (finite presentation implies finite type by the
   definitions), so [lem-kun-finite-type-residue-trdeg] gives finite transcendence degree; an
   algebraically independent generating set in [def-trf-purely-transcendental-extension] therefore
   has finite cardinality. Apply [lem-trf-finite-smooth-integral-base-refinement] to $S_0=A$,
   $Y_0=U$, $n=d$, and $W_0=U$ with $\pi_0=\mathrm{id}_U$ and $w_0=y_0=y'$. The identity is finite
   and its fibre is a singleton by definition. We obtain an affine elementary etale
   $(C,c)\to(A,b')$ and a quasi-compact open $V\subset U\times_A C$, smooth of relative dimension
   $d$ with geometrically integral fibres, containing a point $v$ with residue field $\kappa(y)$;
   also $\kappa(c)=\kappa(b)$.
3. Choose an affine open $W\subset V$ containing $v$ by [lem-weil-pbc-affine-opens-basis]. The
   morphism $V\to C$ is smooth, hence flat and locally of finite presentation by [lem-pc-smooth-
   flat], and open by [lem-weil-pbc-flat-lfp-open]. Thus its image of $W$ is an open neighbourhood
   of $c$. Choose a principal open $B''=D(a)\subset C$ containing $c$ and contained in this image
   by [lem-weil-pbc-spec-localization-away-basic-open]. It is affine with open-immersion inclusion
   by [lem-weil-pbc-principal-localization-open-immersion]. Put $Y''=W\times_C B''$. It is affine
   by [lem-weil-pbc-fibre-product-affine-spectra], and open in $Y'\times_{B'}B''$. Every fibre is
   nonempty, by the choice of $D(a)$, and is an open subscheme of the corresponding geometrically
   integral fibre of $V$. After any field extension it remains nonempty by [lem-pc-field-
   extension-surjective] and [lem-weil-pbc-surjective-base-change], and open in an integral
   scheme, hence irreducible and reduced: any two nonempty opens intersect, and restrictions of a
   reduced structure sheaf are reduced. Thus these fibres are geometrically integral in [def-pc-
   geometrically-irreducible]. Smooth relative dimension $d$ is unchanged by open restriction and
   base change, using [lem-sbc-smooth-relative-dimension-permanence] and the etaleness of open
   immersions. Each fibre $Y''_t$ is irreducible and of finite type over $\kappa(t)$ (an open of
   the finite-type affine $W_t$), and $\dim_{y_1}Y''_t=d$ at its points, so $\dim Y''_t=d$ by
   [lem-sc-dimension-locally-algebraic]. The marked point $y''$ is the restriction of $v$; the
   maps $(B'',b'')\to(B',b')$ and $h:(Y'',y'')\to(Y,y)$ are elementary by composition and open-
   immersion invariance of residue fields.
4. Set $Z''=Z\times_Y Y''$. The morphism $\pi'':Z''\to Y''$ is finite and $Z''$ is affine by [lem-
   weil-pbc-finite-morphism-permanence]. Its projection $e:Z''\to Z$ is etale by [lem-weil-pbc-
   etale-scheme-base-change]. Every point over $y''$ maps to $z$, since $\pi^{-1}(y)=\{z\}$. By
   [lem-weil-pbc-fibre-product-points], these points correspond to primes of
   $\kappa(z)\otimes_{\kappa(y)}\kappa(y'')$. The field map $\beta:\kappa(y)\to\kappa(y'')$ is an
   isomorphism, so $a\otimes b\mapsto a\,\pi^\sharp(\beta^{-1}(b))$ identifies this tensor ring
   with $\kappa(z)$. It has one prime. Denote the resulting point by $z''$. By [lem-weil-pbc-
   fibre-product-point-residue-field], the canonical map $\kappa(z)\to\kappa(z'')$ is an
   isomorphism. This proves the singleton-fibre requirement and the pointed hypothesis for the
   ambient lift.
5. Apply [lem-trf-pointed-etale-ambient-lift] with $S=B$, $S_1=B''$, $W=Z''$, $j=i$, $b=e$, and
   $r:Z''\to Y''\to B''$. Its base and $Z$ residue-field hypotheses were verified in steps 3 and
   4. It supplies an affine $X''$, a closed immersion $i'':Z''\hookrightarrow X''$ of finite
   presentation, an elementary etale $(X'',x'')\to(X,x)$, and the required cartesian square,
   compatibly over $B''\to B$. Here $x''=i''(z'')$. In particular the source morphism to $B''$ is
   locally of finite type: $X\to B$ is finite type because it is locally finite type and quasi-
   compact by [lem-weil-pbc-qcqs-morphism-permanence] and [lem-weil-pbc-affine-scheme-qcqs];
   $X\times_B B''$ is affine by [lem-weil-pbc-fibre-product-affine-spectra], and its map to $B''$
   is finite type by [lem-sfb-finite-type-composition-base-change]. The affine etale map $X''\to
   X\times_B B''$ is of finite presentation, hence finite type, by the same qcqs permanence
   statement. Composing gives finite type, hence locally finite type, over $B''$.
6. Let $g:X''\to X$, and put $\mathcal F''=g^*\mathcal F$, $\mathcal G''=e^*\mathcal G$. They are
   quasi-coherent and of finite type by [lem-weil-pbc-module-pullback-quasi-coherent] and [lem-
   weil-pbc-module-pullback-finite-type]. The closed immersion $i$ is affine: over an affine open
   of $X$ its inverse image is the spectrum of the quotient by its defining ideal [def-weil-
   closed-immersion]. Therefore the cartesian square in step 5 and [lem-weil-pbc-affine-
   pushforward-base-change](1) give $g^*i_*\mathcal G\cong i''_*e^*\mathcal G$. Pull back the
   specified isomorphism $i_*\mathcal G\cong\mathcal F$ to obtain $i''_*\mathcal G''\cong\mathcal
   F''$. Together with steps 3--5, this verifies every condition of [def-trf-pointed-scheme-
   devissage-data]: affineness, marked incidence, singleton finite fibre, smooth geometrically
   irreducible fibres of dimension $d$, finite-presentation closed immersion, and the module
   isomorphism. The field extension $\kappa(y'')/\kappa(b'')$ is the old purely transcendental
   extension through the induced field isomorphisms.
7. The finite morphism $\pi$ is affine by [def-weil-finite-integral-morphism]. Apply [lem-weil-
   pbc-affine-pushforward-base-change](1) to its cartesian base change along $h$. The resulting
   canonical map is the required isomorphism $h^*(\pi_*\mathcal G)\cong\pi''_*\mathcal G''$. In
   particular it identifies the pulled-back $\alpha$ with a map $\alpha'':\mathcal O_{Y''}^{\oplus
   r}\to\pi''_*\mathcal G''$: [lem-weil-pbc-module-pullback-structure-sheaf] identifies the
   structure sheaves, and finite direct sums in the tensor definition [def-pc-module-pullback] are
   carried to finite direct sums.
8. Write $\xi''$ and $\xi$ for the unique generic points of the nonempty irreducible fibres
   $Y''_{b''}$ and $Y_b$. The map $U\to Y\times_B A$ is etale by step 1. Base changing it over $A$
   to $\operatorname{Spec}\kappa(b'')$, then restricting to the open $Y''_{b''}\subset
   U\times_A\operatorname{Spec}\kappa(b'')$, gives an etale $h_b:Y''_{b''}\to Y_b$, since
   $\kappa(b'')=\kappa(b)$, by [lem-weil-pbc-etale-scheme-base-change] and [lem-weil-pbc-etale-
   composition-cancellation]. It is flat and locally of finite presentation by [def-weil-etale-
   morphism], hence open by [lem-weil-pbc-flat-lfp-open]. Its image is a nonempty open of the
   irreducible $Y_b$, so contains $\xi$. On the other hand every point of $Y''_{b''}$ is a
   specialization of $\xi''$, so its image is a specialization of $h_b(\xi'')$ by continuity. In
   particular $\xi$ is a specialization of $h_b(\xi'')$. The only point specializing to the
   generic point of an irreducible scheme is that generic point itself (the two points have the
   same closure and a scheme is $T_0$). Thus $h_b(\xi'')=\xi$.
9. For $\mathcal H=\pi_*\mathcal G$, the natural stalk formula [lem-weil-pbc-module-stalk-
   pullback] and step 8 identify the residue-field map of $h^*\alpha$ at $\xi''$ with
   $$\bigl(\alpha_\xi\otimes_{\mathcal
   O_{Y,\xi}}\kappa(\xi)\bigr)\otimes_{\kappa(\xi)}\kappa(\xi'').$$ Indeed associativity of tensor
   products identifies both its source and target with extension of scalars along the canonical
   field map $\kappa(\xi)\to\kappa(\xi'')$, since the local ring map sends the maximal ideal at
   $\xi$ into that at $\xi''$. Tensoring an isomorphism gives an isomorphism (tensor its inverse),
   so $\alpha''$ has the asserted generic residue-field property.
10. Finally $\mathcal H=\pi_*\mathcal G$ is quasi-coherent by [lem-weil-pbc-affine-pushforward-
   base-change](1), so $\mathcal Q=\operatorname{coker}\alpha$ is quasi-coherent and its sections
   on an affine open are the cokernel of the section map by [lem-weil-pbc-quasi-coherent-module-
   cokernel-image]. For an affine open of $Y''$ over an affine open of $Y$, [lem-weil-pbc-module-
   pullback-affine-sections] computes pullback by tensoring the section modules, naturally in
   $\alpha$. By [lem-weil-pbc-tensor-right-exact], tensoring its cokernel sequence computes the
   cokernel of the tensored map. These natural identifications therefore give the canonical
   isomorphism $\operatorname{coker}\alpha''\cong h^*\mathcal Q$, with its quotient map. Together
   with the canonical pushforward comparison in step 7 and the field isomorphisms in steps 3--4,
   this proves all the remaining assertions.
-/
theorem PointedAffineOneStep.exists_elementaryEtale_refinement
    {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X}
    (s : PointedAffineOneStep f F x)
    {Y' B' : Scheme.{u}} (g' : Y' ⟶ B') (aY : Y' ⟶ s.Y) (aB : B' ⟶ B)
    (y' : Y') (b' : B') (square : aY ≫ s.g = g' ≫ aB)
    (marked : g' y' = b') (targetElementary : IsElementaryEtalePointed aY y' s.y)
    (baseElementary : IsElementaryEtalePointed aB b' (f x)) :
    ∃ (B'' : Scheme.{u}) (cB : B'' ⟶ B') (b'' : B''),
      IsAffine B'' ∧ IsElementaryEtalePointed cB b'' b' ∧
      IsElementaryEtalePointed (cB ≫ aB) b'' (f x) ∧
      ∃ (X'' : Scheme.{u}) (aX : X'' ⟶ X) (f'' : X'' ⟶ B'') (x'' : X'')
        (t : PointedAffineOneStep f'' ((Scheme.Modules.tensorPullback aX).obj F) x'')
        (j : t.Y ⟶ pullback g' cB) (h : t.Y ⟶ s.Y) (e : t.Z ⟶ s.Z),
        IsElementaryEtalePointed aX x'' x ∧ f'' x'' = b'' ∧
        aX ≫ f = f'' ≫ cB ≫ aB ∧
        IsOpenImmersion j ∧
        j ≫ pullback.fst g' cB ≫ aY = h ∧ j ≫ pullback.snd g' cB = t.g ∧
        (j ≫ pullback.fst g' cB) t.y = y' ∧
        IsElementaryEtalePointed h t.y s.y ∧ e t.z = s.z ∧ t.d = s.d ∧
        ∃ (finiteSquare : IsPullback e t.π s.π h)
          (closedSquare : IsPullback e t.i s.i aX)
          (eG : (Scheme.Modules.tensorPullback e).obj s.G ≅ t.G),
          Scheme.Modules.moduleBaseChangeMap s.i t.i aX e closedSquare.w s.G ≫
              (Scheme.Modules.pushforward t.i).map eG.hom ≫ t.presentation.hom =
            (Scheme.Modules.tensorPullback aX).map s.presentation.hom ∧
          ∃ β : (Scheme.Modules.tensorPullback h).obj
              ((Scheme.Modules.pushforward s.π).obj s.G) ≅
                (Scheme.Modules.pushforward t.π).obj t.G,
            β.hom = Scheme.Modules.moduleBaseChangeMap s.π t.π h e finiteSquare.w s.G ≫
              (Scheme.Modules.pushforward t.π).map eG.hom ∧
            ∀ (r : ℕ)
              (α : SheafOfModules.free (R := s.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
                (Scheme.Modules.pushforward s.π).obj s.G),
              (∀ ξ : s.g.fiber (f x), IsGenericPoint ξ Set.univ →
                IsResidueFibreIso α (s.g.fiberι (f x) ξ)) →
              ∃ (α'' : SheafOfModules.free (R := t.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
                  (Scheme.Modules.pushforward t.π).obj t.G),
                α'' = (Scheme.Modules.picardTensorFreeIso h (ULift.{u} (Fin r))).inv ≫
                  (Scheme.Modules.tensorPullback h).map α ≫ β.hom ∧
                (∀ ξ'' : t.g.fiber b'', IsGenericPoint ξ'' Set.univ →
                  IsResidueFibreIso α'' (t.g.fiberι b'' ξ'')) ∧
                ∃ q : (Scheme.Modules.tensorPullback h).obj (cokernel α) ≅ cokernel α'',
                  (Scheme.Modules.tensorPullback h).map (cokernel.π α) ≫ q.hom =
                    β.hom ≫ cokernel.π α'' := by
  sorry

end AlgebraicGeometry
