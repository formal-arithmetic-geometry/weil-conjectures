## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.module_proper_carrier_support`
and `AlgebraicGeometry.AlgebraicSpace.structure_module_proper_carrier_support` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleProperCarrierSupport`. Both proofs are
`sorry`; there are no definitions or instances and no other postponed obligations.
The existing statement and dependency lists are unchanged. No statement correction,
new node or dependency module is needed.

Sources read: Stacks `spaces-perfect.tex`, lemma-module-support-proper-over-base,
Tag 0CZI, especially (2) iff (3); `spaces-morphisms.tex`,
lemma-scheme-theoretic-support and definition-scheme-theoretic-support, Tags 07U0
and 07U1; the recorded closed-ideal correspondence and its source/docstring for
the structural quotient case. These say precisely the carrier equivalence and
the annihilator construction stated in this node.

Hypotheses and clauses, in node order:

- The base scheme is `{S : Scheme.{u}}`; `{X Y : AlgebraicSpace S}` uses the
  existing fppf-sheaf algebraic spaces over that same base. `universe u` is explicit.
  Their existing small etale sites have object universe `u+1`, morphism universe
  `u`, and structure-ring and module sections in `u`; no new equality of size
  parameters or extra hypothesis is introduced.
- The morphism is `f : X ⟶ Y`; the locally-of-finite-type chart hypothesis is
  `hf : MapIsLocally (@LocallyOfFiniteType) f`, not global finite type.
- The module is `M : X.Modules`, with exactly `hMq : M.IsQuasicoherent` and
  `hMt : M.IsFiniteType`. The latter is Mathlib's local finite-generating-section
  predicate on this ringed site, not finite presentation or coherence.
- The annihilator ideal is the existential `A : QuasiCoherentIdeal X`, a
  quasi-coherent subobject of `SheafOfModules.unit X.structureSheaf`. On each
  `U : X.EtaleSite`, membership in the range of its inclusion is equivalent to
  `∀ (V : X.EtaleSite) (r : V ⟶ U) (s : M.val.obj (op V)),
  X.structureSheaf.obj.map r.op a • s = 0`. This includes every further
  restriction and every local section, rather than just sections on U itself.
  Its being quasi-coherent is part of the type of A, hence a conclusion.
- The closed support is `C : ClosedSubspace X`, and the equation
  `A.val = kernelSubobject (moduleStructureMap C.val.arrow)` fixes its exact
  defining ideal. By the recorded closed-ideal correspondence this is the closed
  subspace defined by A; no radical or underlying-point-set replacement occurs.
- The first properness condition is `MapIsProper (C.val.arrow ≫ f)`.
- The equivalence is `↔ ∃ (W : AlgebraicSpace S) (j : W ⟶ X) (G : W.Modules), ...`.
  Its conditions are representability by scheme closed immersions,
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) j.hom.hom`,
  properness `MapIsProper (j ≫ f)`, the two predicates `G.IsQuasicoherent`
  and `G.IsFiniteType`, and `Nonempty ((moduleDirectImage j).obj G ≅ M)`.
  This is precisely the stated proper closed carrier with its module.
- The second theorem quantifies over every `C : ClosedSubspace X`. Such a
  subobject represents a closed immersion up to isomorphism over X, the correct
  identification for scheme-theoretic support. Its module is literally
  `(moduleDirectImage C.val.arrow).obj
  (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf)`.
  The first two conjuncts state this module's quasi-coherence and finite type.
  The third identifies its annihilator, on all restricted sections as above,
  with the kernel ideal of that very C. The closed-ideal bijection thus says
  that the support of the structural direct image is C itself, including its
  scheme structure. The last conjunct says existence of the same proper closed
  carrier is equivalent to `MapIsProper (C.val.arrow ≫ f)`.
- There is no Noetherian or flatness hypothesis anywhere, and the structure
  quotient case has no finite-generation hypothesis on its defining ideal.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `EtaleSite`, `structureSheaf`, `Modules`; these retain
  the original small-etale ringed-site construction.
- `def-weil-size-convention` is the metatheoretic universe convention, not a
  declaration to redefine or an object binder.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, applied to every scheme-test projection.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent `SheafOfModules` specialization used by `X.Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with the
  identical underlying Mathlib predicate `SheafOfModules.IsQuasicoherent`.
  `SheafOfModules.IsFiniteType` was read in Mathlib's `Sheaf/Generators.lean`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`
  and its chart-limit model; `moduleTensorPullback`, `moduleTensorAdjunction`.
  The direct image in the conclusions is that specified canonical functor.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`
  and `MapIsProper`, including the separated, finite-type and universally
  closed definitions, with the original chart and point-map tests.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence`:
  `closed_ideal_correspondence`, including its full quotient and base-change
  interface. Its public dependencies provide `ClosedSubspace`,
  `QuasiCoherentIdeal` and `moduleStructureMap`. The kernel and quotient clauses
  identify the support and justify the structural direct-image corollary.

The primary public imports expose all statement dependencies transitively.
Every recorded proof-dependency module available in the read clone is imported
privately: SchemeZariskiEtaleQuasiCoherentEquivalence, AlgebraicSpaceAffineChartCalculus,
WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport, Mathlib's Etale,
AnnihilatorFiniteFlatBaseChange, AlgebraicSpaceIdealClosedSubspaceCorrespondence,
AlgebraicSpaceEtaleModulePushforwardRestriction, and the upstream
ClosedImmersionPushforwardAnnihilated. The closed-ideal correspondence is already
public. These proof nodes have no Lean record in the read DAG, so there is no module
to import yet: lem-sfb-space-qcoh-cartesian-chart-family,
lem-sfb-space-closed-immersion-quasi-coherent-modules,
lem-sfb-space-closed-subspace-proper, lem-sfb-space-proper-composition. They are
proof prerequisites, not missing notions for either delivered statement.

Edge cases checked before writing and again after compilation:

- M=0: the annihilator is the whole structure sheaf and C is empty; the zero
  module has an empty proper carrier even if X is not proper over Y.
- Empty X or empty closed subspace: all local-section assertions and both
  proper-carrier statements retain these cases, without a nonempty binder.
- A non-finitely-generated ideal I: O/I is still cyclic on affine etale charts,
  so finite type of the structural quotient does not force I to be finite type.
- Nilpotents, for example the quotient of k[e]/(e^2) by (e): the equality of
  kernel and annihilator ideals retains (e), rather than replacing it by a
  point-set support condition. For M=O on the same ring the annihilator is zero,
  so the full nonreduced scheme structure is retained.
- M=O on the affine line over a field: its support is the whole affine line;
  neither properness nor a proper closed carrier can hold. The carrier
  existential does not accidentally assert properness for every module.
- f is only locally of finite type; no quasi-compactness of f, separation of f,
  flatness or Noetherian hypothesis is smuggled into the inputs.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder` with "A finite type quasi coherent module on an
  algebraic space has proper scheme theoretic support if and only if it is a
  direct image from a proper closed subspace": eight hits, all scheme
  properness or scheme ideal support facts, no algebraic-space carrier theorem.
- `msearch.py ... loogle '"support", "IsProper"'`: zero hits.
- `msearch.py ... grep 'annihilator|properCarrier|schemeTheoreticSupport'
  AlgebraicGeometry`: four hits, all elementary annihilator-span calculations
  in Mathlib/AlgebraicGeometry/SpreadingOut.lean, no matching statement.
- `msearch.py ... leansearch` with "The annihilator of a finite type quasi
  coherent module on an algebraic space defines a closed subspace with proper
  support if and only if the module has a proper closed carrier": eight hits,
  ordinary Module/Submodule annihilators and support, no such theorem.
- `rg` in `lean/WeilConjectures` for support/proper-support and
  schemeTheoreticSupport found scheme results, including the recorded scheme
  support dependency; searching the node id itself found no declaration.
- `rg` in `lean/Sheaf` found `HasProperAnnihilatorSupport` in
  AlgebraicSpaceFlatProperCoefficient, a predicate asserting a proper
  annihilator support on scheme charts, not the existence/ideal/carrier theorem.
  The existing ClosedSubspace, QuasiCoherentIdeal and moduleStructureMap suffice;
  no second definition of any of those notions was introduced.
- The two proposed declaration names were searched in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  no existing declaration with either name.

Validation: the prescribed `scompile.py O4 lem-sfb-space-module-proper-carrier-support`
compiled the delivered file in sandbox and library-module modes, respectively
2.3 s and 2.2 s, with no errors or unexpected warnings. The module starts with
`module`, uses public imports for the statement and private proof imports,
exposes its declarations, disables autoImplicit, and declares its universe.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by O4

A separate rereading of the node, both signatures and the source passages found
no mismatch. This is the worker's rereading; the dispatcher explicitly forbids
starting other agents, and the maintainer supplies the independent review.

In particular, I checked that the annihilator quantifies over all restrictions,
not just over sections on U; that quasi-coherence of A is concluded rather than
assumed; that its equality with the kernel fixes the closed support; that the
carrier's module is required to be both finite type and quasi-coherent; and
that the isomorphism uses the recorded moduleDirectImage. I reread the second
theorem's conjunctions: the annihilator is that of the structural direct image,
the kernel is that of the original C, and the final equivalence involves that
same C. Thus neither nilpotents nor arbitrary closed immersions were lost.
All binders are explicit, and neither theorem has a Noetherian or flatness
assumption. No changes were needed after the first successful compile.
