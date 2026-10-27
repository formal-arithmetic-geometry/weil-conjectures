## Worker report

Item: lem-sfb-closed-ideal-base-change-affine-diagram. Stage 2, Q46.
The only node change is its Lean record. The accepted stage-1 statement, split,
source, dependencies and reviews remain unchanged. The inherited stage-1 refusal
is superseded by the explicit stage-2 handoff in brief-stage2 section 0; the live
queue lists this item at stage 2 and the live node has no Lean declaration.
There is no repair note for this item and no Q46 return entry for it.

The module Sheaf.AlgebraicGeometry.ClosedIdealBaseChangeAffineDiagram has one
postponed theorem, AlgebraicGeometry.closedIdealBaseChange_affineDiagram, with
its eight-step natural-language proof in the docstring. Its three full helper
definitions package the actual induced morphism, actual ideal arrow and affine
clause of this same node. They introduce no independent mathematical notion,
no arbitrary map and no new choice. No theorem is proved in this delivery.

Hypotheses and clause correspondence:

- Schemes X,Z,T,T' and maps f,i,g are explicit binders at arbitrary universe u.
  The only geometric hypothesis is [IsClosedImmersion i]. There is no flatness,
  finite type, Noetherian, separatedness, nonempty or nontrivial-ring assumption.
- X' is Limits.pullback f g and Z' is Limits.pullback (i ≫ f) g; h is its first
  projection and the other projection is pullback.snd f g.
  closedIdealBaseChangeMap is pullback.map with i, identity and identity, with
  the two commutations supplied by simp; it is the induced i' of the statement.
- The ideal I is i.ker.toModules and the inclusion is i.ker.toModulesι.
  The named closedIdealBaseChangeArrow is (tensorPullback h).map of that
  inclusion followed by tensorPullbackObjUnitToUnit h. The latter is the existing
  map adjoint to the structure-ring map under the normalized tensor adjunction.
- IsPullback (pullback.fst (i ≫ f) g) i' i h is the identification
  Z' ≅ Z ×_X X' with both projections; the chosen i' already preserves the
  T' projection by the definition of pullback.map. This universal-property
  formulation includes the projection-compatible isomorphism uniquely.
- IsClosedImmersion i' is the closedness conclusion.
  Subobject.mk (kernel.ι (unitToPushforwardObjUnit i')) = imageSubobject a
  is exactly ker b = im a in the common structure module. No monomorphism
  condition is imposed on a.
- The next three IsQuasicoherent conjuncts refer, respectively, to h*I, O_X'
  and i'_*O_Z'. Quasi-coherent here is the existing Mathlib predicate, rather
  than the unrelated finite-type part of pqf-def-coherent.
- The existential w is just the cartesian commutation equation; its proof is
  an argument to the existing canonical moduleBaseChangeMap, not an extra
  hypothesis. Composing that map with i'_*tensorPullbackObjUnitToUnit on Z'
  gives the canonical comparison h*i_*O_Z → i'_*O_Z'. IsIso is its invertibility.
  The following morphism equation is the square saying that it sends the
  pulled-back quotient to epsilon_h followed by b. This states the quotient
  clause before identifying h*O_X with O_X' by epsilon_h.
- The forall V,U,V',hf,hg clause covers every triple of affine opens with
  f(U) contained in V and g(V') contained in V. It unfolds the full
  closedIdealBaseChangeAffineChart predicate, with no affine hypothesis on
  arbitrary intersections. Its definitions R=Γ(T,V), A=Γ(X,U), R'=Γ(T',V')
  use the actual induced maps f.appLE and g.appLE for both algebra structures.
- Q is h⁻¹U intersect k⁻¹V'. The chart predicate asserts IsAffineOpen Q,
  IsAffineOpen (i'⁻¹Q), and IsAffineOpen (i⁻¹U). Its IsPullback of the restricted
  projections says precisely Q = U ×_V V'. Combined with the global cartesian
  square, this also identifies i'⁻¹Q = (i⁻¹U) ×_V V'.
- J is the existing ideal i.ker.ideal U and B is A/J. The additive equivalence
  eI: J ≃+ Γ(I,U) is fixed by inclusion(eI j)=j. The ring equivalence
  eB: B ≃+* Γ(Z,i⁻¹U) is fixed by eB(quotient x)=i.app U x. Thus i⁻¹U is
  Spec B with its specified quotient map, not an arbitrary affine model.
- The ring equivalences eA: Γ(X',Q) ≃+* A⊗_R R' and
  eB': Γ(Z',i'⁻¹Q) ≃+* B⊗_R R', together with affineness, express the stated
  Spec identifications. The eA.symm pure-tensor equation fixes both projections.
  The b equation fixes eB' by eB'(b(eA.symm(x⊗r)))=quotient(x)⊗r, hence fixes
  the quotient projection; the quotient map is surjective on this affine open.
- c is an additive equivalence J⊗_A(A⊗_R R') ≃+ Γ(h*I,Q). Its generator formula
  is c(j⊗d)=eA.symm(d) times the restriction to Q of eta(eI j), using the
  recorded tensorPullbackSectionAdjunction. The next clause imposes linearity
  for all A'=A⊗_R R' scalars. Thus this is the required module comparison,
  not merely an additive identification.
- The balanced isomorphism is the existing
  TensorProduct.AlgebraTensorModule.cancelBaseChange R A A J R'. Both its
  displayed forward formula j⊗(x⊗r) ↦ (x•j)⊗r and inverse formula
  j⊗r ↦ j⊗(1⊗r) occur verbatim as conjuncts of the chart predicate.
- The next conjunct is a_Q(c(j⊗d))=(j⊗1)d in eA coordinates; the following
  one is b_Q(x⊗r)=quotient(x)⊗r in eB' coordinates. The final conjunct gives
  a_Q(c(balanced.symm(j⊗r)))=j⊗r, explicitly expressing the section sequence
  in the J⊗_R R' coordinates specified in the node.
- The last forall q, exists V,U,V' clause states that every point lies in one
  of these Q, with the same two image containments. Empty schemes are included.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst, pullback.snd, pullback.map; Mathlib.AlgebraicGeometry.Pullbacks
  supplies the scheme pullbacks and their affine descriptions.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: Scheme.Hom.ker, ker_apply;
  WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module: toModules,
  toModulesι. The latter constructs a genuine kernel, not unknown sheaf data.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: tensorPullback,
  tensorPullbackSectionAdjunction, including its uniquely section-normalized
  unit. WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf:
  tensorPullbackObjUnitToUnit, whose definition uses the same normalized unit.
- Sheaf.AlgebraicGeometry.CoherentFiniteType imports the Mathlib module
  predicate SheafOfModules.IsQuasicoherent required by pqf-def-coherent.
- WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction:
  moduleBaseChangeMap is the actual adjoint-defined comparison used here.
- Mathlib.LinearAlgebra.TensorProduct.Tower:
  TensorProduct.AlgebraTensorModule.cancelBaseChange.
- Plain proof imports: ClosedSubschemeBaseChangeIdealImage,
  AffinePushforwardBaseChange and ModulePullbackAffineSections (all under
  WeilConjectures.AlgebraicGeometry), for the proof-dependency interfaces.

Source reading: schemes.tex lemma-fibre-product-immersion (01JU),
lemma-open-fibre-product (01JR), lemma-fibre-product-affines (01JQ),
lemma-widetilde-pullback (01I9), and coherent.tex lemma-affine-base-change
(02KG), including its explicit balanced tensor identity. These impose no
flatness or finiteness condition. The node is an agent-assembled normalization
of these facts, as its source and proof_origin already record.

Edge cases checked mathematically before writing: J=0 gives zero first term
and the identity quotient; J=A gives the unit ideal and empty closed subscheme;
empty schemes and empty chart opens are allowed, as are zero rings. With
R=A=Z, J=(2), R'=F_2, the first tensor map is zero and the quotient is the
identity. In particular replacing im a by an injected copy of h*I would be
false; the delivery preserves the image-only claim. No affine-intersection or
separatedness shortcut is used. The algebra structures are fixed by the
original maps even when they are noninjective or nonsurjective.

Searches (prescribed msearch.py, Q46/item; all 2026-10-23):

- LeanFinder: "Canonical affine diagram for base change of a closed immersion
  ideal sequence with pure tensor formulas" returned eight component results,
  including pullbackSpecIso, closed quotient immersion and Spec tensor squares;
  none is the complete statement.
- Loogle: "AlgebraicGeometry.Scheme.IdealSheafData.comap,
  AlgebraicGeometry.pullbackSpecIso" returned zero hits.
- Mathlib grep: "ker_fst|toModulesι|comap" in AlgebraicGeometry/IdealSheaf
  returned fifteen hits, including comap and comapIso, but no module sequence
  comparison with normalized affine sections.
- LeanSearch: "Base change closed immersion ideal sections tensor canonical
  affine diagram" returned eight closed-immersion component results, including
  Spec_iff, stability under base change and the affine characterization.
- rg in lean/WeilConjectures and lean/Sheaf for closed ideals, base change and
  the exact item id found the component interfaces read above and no existing
  declaration of this item. Searches of TensorProduct/Tower found the exact
  balanced isomorphism, which is reused rather than reconstructed.

No statement correction, disputed assertion, new node, or dependency repair
is needed. The example CompactObject module currently is a withdrawn empty
module, so its legacy example header could not be copied; this delivery uses
module mode, public statement imports, exposed public declarations, explicit
universes and disabled auto-implicits as the current brief requires.

Validation: every Lean file is compiled only through scompile.py; no global
build or direct repository mutation. The module compiled in both the scratch
and actual module namespaces; a long docstring line was shortened afterwards.
The final dry-run and push results are recorded by the delivery wrappers.

## Second reading by Q46

This is the worker's self-check, not a claim of an independent second worker.
The dispatch explicitly forbids starting another agent and assigns independent
reading to the maintainer. I reread the node and the complete module together:
the first draft resolved pullback inside Scheme.Modules to module pullback;
I moved the declarations to AlgebraicGeometry and opened Scheme.Modules, which
preserves the scheme fibre products. I corrected the balanced isomorphism's
full namespace and explicitly typed the point binder as Scheme.{u}. All of
these were elaboration repairs; no source hypothesis or conclusion changed.
The correspondence above checks every chart normalization, including both
balanced formulas and the cover clause, rather than only the global ideal image.
