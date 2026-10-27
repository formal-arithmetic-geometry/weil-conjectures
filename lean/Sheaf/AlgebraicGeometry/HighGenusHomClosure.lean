/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import WeilConjectures.AlgebraicGeometry.GenericFibreIsoSpreadBaseOpen
import Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso

/-! # Projective closure of a generic morphism from a nodal curve family

Source: de Jong, Families of curves and alterations, §§3.9--3.12, Claim 3.10 and
Lemma 3.13, printed p.609 (blueprint: lem-sfb-high-genus-hom-closure).

The node generalizes the target condition to the absence of nonconstant geometric
projective-line maps. The representing scheme is specified by its universal evaluation.
Its reduced closure is the actual vanishing-ideal subscheme, not an arbitrary modification.
Naturality and the resulting group action are stated separately below.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Change the parameter in the source of a relative morphism.
Source: de Jong §3.9, universal evaluation
(blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def homParameterMap {S W T M : Scheme.{u}} (f : W ⟶ S) (t : T ⟶ S) (p : M ⟶ S)
    (a : T ⟶ M) (ha : a ≫ p = t) : pullback f t ⟶ pullback f p :=
  pullback.map f t f p (𝟙 W) a (𝟙 S) (by simp) (by simpa using ha.symm)

/-- A scheme representing relative morphisms, with its universal evaluation. A map
`W_T ⟶ Q` over `S` is the same as a `T`-map `W_T ⟶ Q_T`, by the pullback property.
The uniqueness condition therefore represents exactly `Hom_T(W_T,Q_T)` on every test scheme.
The disjoint open cover records a disjoint union of quasi-projective schemes: each piece
is an open subscheme of an H-projective scheme over the base.
Source: de Jong §3.9 and Stacks Tags 0D1A--0D1B
(blueprint: lem-sfb-high-genus-hom-closure). -/
structure RelativeHomSchemeData {S W Q : Scheme.{u}} (f : W ⟶ S) (g : Q ⟶ S) where
  parameter : Scheme.{u}
  projection : parameter ⟶ S
  evaluation : pullback f projection ⟶ Q
  evaluation_over : evaluation ≫ g = pullback.fst f projection ≫ f
  universal : ∀ (T : Scheme.{u}) (t : T ⟶ S) (z : pullback f t ⟶ Q),
    z ≫ g = pullback.fst f t ≫ f →
      ∃! a : T ⟶ parameter, ∃ ha : a ≫ projection = t,
        homParameterMap f t projection a ha ≫ evaluation = z
  pieces : ∃ (I : Type u) (U : I → parameter.Opens),
    iSup U = ⊤ ∧ Pairwise (fun i j : I ↦ Disjoint (U i) (U j)) ∧
      ∀ i : I, ∃ (P : Scheme.{u}) (p : P ⟶ S) (b : (U i).toScheme ⟶ P),
        IsHProjective p ∧ IsOpenImmersion b ∧ b ≫ p = (U i).ι ≫ projection

namespace RelativeHomSchemeData

variable {S W Q E : Scheme.{u}} {f : W ⟶ S} {g : Q ⟶ S}

/-- The vanishing ideal of the closure of the generic Hom point.
Source: de Jong §3.9 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def closureIdeal (D : RelativeHomSchemeData f g) (m : E ⟶ D.parameter) :
    D.parameter.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range m))

/-- The reduced closure, constructed using the vanishing ideal.
Source: de Jong §3.9 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def closureScheme (D : RelativeHomSchemeData f g) (m : E ⟶ D.parameter) :
    Scheme.{u} :=
  (D.closureIdeal m).subscheme

/-- Inclusion of the reduced closure into the morphism scheme.
Source: de Jong §3.9 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def closureInclusion (D : RelativeHomSchemeData f g)
    (m : E ⟶ D.parameter) : D.closureScheme m ⟶ D.parameter :=
  (D.closureIdeal m).subschemeι

/-- Structure morphism of the reduced closure.
Source: de Jong §§3.9--3.11 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def closureProjection (D : RelativeHomSchemeData f g)
    (m : E ⟶ D.parameter) : D.closureScheme m ⟶ S :=
  D.closureInclusion m ≫ D.projection

/-- Restriction of universal evaluation to the reduced closure, followed by `Q_R ⟶ Q`.
Source: de Jong §3.11 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def closureEvaluationToTarget (D : RelativeHomSchemeData f g)
    (m : E ⟶ D.parameter) : pullback f (D.closureProjection m) ⟶ Q :=
  homParameterMap f (D.closureProjection m) D.projection (D.closureInclusion m) rfl ≫
    D.evaluation

/-- The actual evaluation `W_R ⟶ Q_R`, obtained from the restricted universal evaluation
by the fibre-product universal property.
Source: de Jong §3.11 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def closureEvaluation (D : RelativeHomSchemeData f g)
    (m : E ⟶ D.parameter) :
    pullback f (D.closureProjection m) ⟶ pullback g (D.closureProjection m) :=
  pullback.lift (D.closureEvaluationToTarget m) (pullback.snd f (D.closureProjection m))
    (by simp [closureEvaluationToTarget, homParameterMap, Category.assoc,
      D.evaluation_over, pullback.condition, closureProjection])

end RelativeHomSchemeData

/-- Existence and geometry of the reduced generic Hom closure. The generic source map is
written over `Spec k(S)` using the generic stalk, so the supplied `u` is precisely a
function-field morphism. All geometric test fields have the scheme universe, as in Mathlib.

Source: de Jong §§3.9--3.12, Claim 3.10 and Lemma 3.13, printed p.609
(blueprint: lem-sfb-high-genus-hom-closure).

Proof (the node's Steps 1--8):
1. A finite-type scheme over a field is Noetherian. Projective base change and H-projective
   composition embed `W ×_S Q` into finite projective space. H-projectivity implies properness.
2. Projective Hilbert-polynomial representability gives projective Hilbert pieces. Graphs
   form an open subfunctor, giving the displayed representing scheme, its quasi-projective
   pieces and universal evaluation (lem-sfb-projective-hilbert-polynomial-representability,
   lem-sfb-graphs-open-in-hilbert).
3. The generic point belongs to one open-and-closed Hilbert piece. Its reduced closure is
   integral, finite type and separated, with generic fibre `Spec K`. Restrict evaluation.
4. Apply lem-sfb-generic-dvr-properness-criterion. Over a DVR in `K`, take the reduced closure
   of the graph in the base-changed projective product. Its projection to the nodal source
   is projective and generically an isomorphism. Projective-nodal-family geometry preserves
   the fibre hypotheses on this trait.
5. Apply lem-sfb-nodal-trait-rational-domination: the source is normal integral and a proper
   dominating resolution has fibres that are points or connected unions of projective lines.
   Every line maps constantly by the target hypothesis. Connectedness makes all constants
   agree, so the graph projection has finite fibres.
6. Proper with finite fibres implies finite (thm-pqf-finite-iff-proper-finite-fibres).
   Finite birational over normal is an isomorphism (lem-trf-finite-birational-normal-iso).
   Its inverse gives the extension, including when the generic map is constant.
7. The representing property gives a trait map to the morphism scheme; generic vanishing
   of the closure ideal makes it factor through the closure. The DVR criterion proves properness.
8. The immersion in the projective Hilbert piece is proper by proper-to-separated, hence
   closed by proper-immersion-closed. This gives H-projectivity. Spread the generic fibre
   isomorphism on affine neighbourhoods using generic-fibre-iso-spread-base-open. Properness
   removes the image of the complement, giving an isomorphism over a dense open of `S`.
-/
theorem exists_projective_generic_hom_closure
    (k : Type u) [Field k] (S W Q : Scheme.{u}) (pS : S ⟶ Spec (.of k))
    [IsIntegral S] [IsHProjective pS] [LocallyOfFiniteType pS]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : W ⟶ S) (g : Q ⟶ S) [IsHProjective f] [Flat f]
    [LocallyOfFinitePresentation f] [IsHProjective g]
    (hnodal : HasNodalGeometricFibres f)
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
      IsReduced (pullback f t))
    [Smooth (pullback.snd f (S.fromSpecStalk (genericPoint S)))]
    [GeometricallyIntegral (pullback.snd f (S.fromSpecStalk (genericPoint S)))]
    (hnoRational : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
      (a : ProjectiveLine (Spec (.of Ω)) ⟶ pullback g t),
      a ≫ pullback.snd g t = ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) →
        ∃ (q : Spec (.of Ω) ⟶ pullback g t),
          q ≫ pullback.snd g t = 𝟙 _ ∧
          a = (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) ≫ q)
    (uη : pullback f (S.fromSpecStalk (genericPoint S)) ⟶
      pullback g (S.fromSpecStalk (genericPoint S)))
    (huη : uη ≫ pullback.snd g (S.fromSpecStalk (genericPoint S)) =
      pullback.snd f (S.fromSpecStalk (genericPoint S))) :
    ∃ (D : RelativeHomSchemeData f g)
      (m : Spec S.functionField ⟶ D.parameter)
      (hm : m ≫ D.projection = S.fromSpecStalk (genericPoint S)),
      homParameterMap f (S.fromSpecStalk (genericPoint S)) D.projection m hm ≫
        D.evaluation = uη ≫ pullback.fst g (S.fromSpecStalk (genericPoint S)) ∧
      IsIntegral (D.closureScheme m) ∧ IsHProjective (D.closureProjection m) ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (D.closureProjection m ∣_ U)) ∧
      ∃ (a : Spec S.functionField ⟶ D.closureScheme m)
        (ha : a ≫ D.closureProjection m = S.fromSpecStalk (genericPoint S)),
        a ≫ D.closureInclusion m = m ∧
        homParameterMap f (S.fromSpecStalk (genericPoint S)) (D.closureProjection m) a ha ≫
          D.closureEvaluation m ≫ pullback.fst g (D.closureProjection m) =
          uη ≫ pullback.fst g (S.fromSpecStalk (genericPoint S)) := by
  sorry

/-- Compatible isomorphisms of the base, source, target and generic scheme induce unique
isomorphisms of the representing schemes and of the actual reduced closures. Both universal
and restricted evaluations commute with these isomorphisms. The uniqueness includes identity
and composition compatibility, and allows isomorphisms that act on the ground field.

Source: de Jong §3.11 (blueprint: lem-sfb-high-genus-hom-closure).

Proof (Step 9 of the node): conjugation by the source and target isomorphisms gives an
isomorphism of relative morphism functors over the transported base. The representing
property gives the unique parameter isomorphism with the evaluation identity. The generic
compatibility takes the specified point to the specified point. An isomorphism carries its
topological closure and its vanishing ideal to the corresponding closure and ideal. Restrict
it and its inverse to obtain the unique closure isomorphism and its evaluation identity.
Identity and composition follow from uniqueness. No projective embedding is preserved or used.
-/
theorem generic_hom_closure_natural
    {S W Q E S' W' Q' E' : Scheme.{u}}
    (f : W ⟶ S) (g : Q ⟶ S) (f' : W' ⟶ S') (g' : Q' ⟶ S')
    (D : RelativeHomSchemeData f g) (D' : RelativeHomSchemeData f' g')
    (j : E ⟶ S) (j' : E' ⟶ S')
    (m : E ⟶ D.parameter) (m' : E' ⟶ D'.parameter)
    (hm : m ≫ D.projection = j) (hm' : m' ≫ D'.projection = j')
    (eS : S ≅ S') (eW : W ≅ W') (eQ : Q ≅ Q') (eE : E ≅ E')
    (hf : f ≫ eS.hom = eW.hom ≫ f') (hg : g ≫ eS.hom = eQ.hom ≫ g')
    (hj : j ≫ eS.hom = eE.hom ≫ j')
    (hu : pullback.map f j f' j' eW.hom eE.hom eS.hom hf hj ≫
        homParameterMap f' j' D'.projection m' hm' ≫ D'.evaluation =
      homParameterMap f j D.projection m hm ≫ D.evaluation ≫ eQ.hom) :
    ∃! eM : D.parameter ≅ D'.parameter,
      ∃ hM : D.projection ≫ eS.hom = eM.hom ≫ D'.projection,
        pullback.map f D.projection f' D'.projection eW.hom eM.hom eS.hom hf hM ≫
          D'.evaluation = D.evaluation ≫ eQ.hom ∧
        m ≫ eM.hom = eE.hom ≫ m' ∧
        ∃! eR : D.closureScheme m ≅ D'.closureScheme m',
          ∃ hR : D.closureProjection m ≫ eS.hom = eR.hom ≫ D'.closureProjection m',
            eR.hom ≫ D'.closureInclusion m' = D.closureInclusion m ≫ eM.hom ∧
            pullback.map f (D.closureProjection m) f' (D'.closureProjection m')
                eW.hom eR.hom eS.hom hf hR ≫ D'.closureEvaluationToTarget m' =
              D.closureEvaluationToTarget m ≫ eQ.hom := by
  sorry

/-- The canonical action of compatible source and base automorphisms on the generic source.
The action on `Spec k(S)` is obtained from the actual generic-stalk automorphism.
Source: de Jong §3.11 (blueprint: lem-sfb-high-genus-hom-closure). -/
noncomputable def genericHomSourceAction
    {S W : Scheme.{u}} [IsIntegral S] (f : W ⟶ S) (eW : Aut W) (eS : Aut S)
    (hf : f ≫ eS.hom = eW.hom ≫ f) :
    pullback f (S.fromSpecStalk (genericPoint S)) ⟶
      pullback f (S.fromSpecStalk (genericPoint S)) :=
  pullback.map f (S.fromSpecStalk (genericPoint S))
    f (S.fromSpecStalk (genericPoint S)) eW.hom
    (Spec.map (Scheme.functionFieldAut eS).hom) eS.hom hf
    (Scheme.SpecMap_functionFieldAut_hom_fromSpecFunctionField eS).symm

/-- A finite group acting compatibly on the datum and its generic morphism acts on the
morphism scheme and its reduced closure, with equivariant evaluation. Actions are arbitrary
scheme actions, so faithfulness and linearity over the ground field are not required.
The generic action is induced canonically by the base action, with no extra action datum.

Source: de Jong §3.11 (blueprint: lem-sfb-high-genus-hom-closure).

Proof (Step 10 of the node): apply Step 9, `generic_hom_closure_natural`, to each group
element, using its canonical generic-stalk isomorphism. The conjugation formula respects
identity and composition. Uniqueness of the induced parameter maps and their restrictions
proves the monoid-homomorphism laws. The two evaluation identities are exactly the
corresponding naturality identities. The generic compatibility makes the reduced closure
invariant. This argument also applies to semilinear actions.
-/
theorem generic_hom_closure_group_action
    {S W Q : Scheme.{u}} [IsIntegral S] (f : W ⟶ S) (g : Q ⟶ S)
    (D : RelativeHomSchemeData f g)
    (m : Spec S.functionField ⟶ D.parameter)
    (hm : m ≫ D.projection = S.fromSpecStalk (genericPoint S))
    (G : Type v) [Group G] [Finite G]
    (σS : G →* Aut S) (σW : G →* Aut W) (σQ : G →* Aut Q)
    (hf : ∀ a : G, f ≫ (σS a).hom = (σW a).hom ≫ f)
    (hg : ∀ a : G, g ≫ (σS a).hom = (σQ a).hom ≫ g)
    (hu : ∀ a : G,
      genericHomSourceAction f (σW a) (σS a) (hf a) ≫
          homParameterMap f (S.fromSpecStalk (genericPoint S)) D.projection m hm ≫
            D.evaluation =
        homParameterMap f (S.fromSpecStalk (genericPoint S)) D.projection m hm ≫
          D.evaluation ≫ (σQ a).hom) :
    ∃ (σM : G →* Aut D.parameter) (σR : G →* Aut (D.closureScheme m))
      (hM : ∀ a : G, D.projection ≫ (σS a).hom = (σM a).hom ≫ D.projection)
      (hR : ∀ a : G,
        D.closureProjection m ≫ (σS a).hom = (σR a).hom ≫ D.closureProjection m),
      (∀ a : G, m ≫ (σM a).hom = Spec.map (Scheme.functionFieldAut (σS a)).hom ≫ m) ∧
      (∀ a : G, (σR a).hom ≫ D.closureInclusion m =
        D.closureInclusion m ≫ (σM a).hom) ∧
      (∀ a : G,
        pullback.map f D.projection f D.projection (σW a).hom (σM a).hom (σS a).hom
            (hf a) (hM a) ≫ D.evaluation = D.evaluation ≫ (σQ a).hom) ∧
      (∀ a : G,
        pullback.map f (D.closureProjection m) f (D.closureProjection m)
            (σW a).hom (σR a).hom (σS a).hom (hf a) (hR a) ≫
              D.closureEvaluationToTarget m = D.closureEvaluationToTarget m ≫ (σQ a).hom) := by
  sorry

end AlgebraicGeometry
