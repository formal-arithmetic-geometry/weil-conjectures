## Worker report

The module `Sheaf.AlgebraicGeometry.SplitTorusCharacterPushout` states
`AlgebraicGeometry.SplitTorusCharacterPushout.character_pushout`. Its only postponed
proof is this named theorem; the action, presheaf coequalizer, sheafification,
canonical class arrow, quotient-point evaluation and base conversions have real data.
`Geometry` is an existential proposition giving the full conclusion, and no representing
scheme or line module is selected from a bare existence theorem.

The accepted stage-1 statement and proof remain unchanged. The inherited BLOCKED
message was the stage-1 live-wins gate, not a failure of this stage-2 assignment:
brief-stage2 §0 explicitly distinguishes these stages. This packet repairs the independent review of returned immutable head
558e64ce1221. The saved Lean source is retained; the ownership dependency is repaired below.

Hypotheses, individually:

- The field is `{k : Type u} [Field k]`.
- `G B : Grp (Over (Spec (.of k)))` are group schemes over exactly this field.
  `IsCommMonObj G.X` and `IsCommMonObj B.X` express commutativity.
- `Smooth G.X.hom`, `Smooth B.X.hom` express smoothness of both structure maps.
- The two `IsClosedImmersion (pullback.diagonal ...)` instances give the specified
  meaning of separatedness, without replacing it by an unspecified predicate.
- `LocallyOfFiniteType` and `QuasiCompact` of each structure map express finite type.
- `r : ℕ` includes rank zero. `MultiplicativeType.splitTorus k r` is the existing
  recursively constructed finite product of the recorded Laurent multiplicative group.
- `i` and `q` are morphisms in the category of group objects, hence homomorphisms.
  `_hkernel : IsPullback ... q.hom.hom η[B.X]` identifies T with the actual kernel.
  `_hlocallySurjective` on `Scheme.fppfTopology.over (Spec (.of k))` says precisely
  that all B-sections lift fppf locally, on all schemes over k.
- `chi` is a morphism of schemes over k to the recorded multiplicative group;
  `[IsMonHom chi]` specifies exactly that it is a group-scheme homomorphism.

Conclusions and constructions, individually:

- `action` is the actual morphism `(g,z,t) ↦ (g i(t), chi(t)⁻¹ z)`.
  `orbitPresheaf` is the presheaf coequalizer of action and projection, which is
  computed pointwise. For a group action this is precisely the orbit quotient.
- `pushoutSheaf` applies actual fppf `sheafify` to this coequalizer. `classMap` is
  `coequalizer.π` followed by `toSheafify`. No unspecified quotient map is assumed.
- The witnesses `E` and `rep` in `Geometry` give a group scheme representing this
  very sheafification; `IsCommMonObj E.X` and `Good E.X.left E.X.hom` assert its
  commutativity, smoothness, closed diagonal and finite type. `rep` is an
  isomorphism of presheaves with lifted Yoneda, natural in every test scheme.
- `bracket rep g z` is transported through `rep.inv` from the actual canonical
  class of `(g,z)`. The first quantified equation in `Geometry` is exactly
  `[gh,zw]=[g,z][h,w]`, specifying the induced multiplication.
- Witnesses `j` and `p`, their `IsMonHom` clauses, and the next two quantified
  equations specify `z ↦ [1,z]` and `[g,z] ↦ q(g)` as homomorphisms.
- `IsPullback j (toUnit ...) p η[B.X]` identifies j with the kernel;
  `Presheaf.IsLocallySurjective ... (yoneda.map p)` gives the fppf epimorphism.
  Together they express the entire asserted exact sequence.
- `M` and `M.IsInvertible` give the invertible O_B-module M_chi.
  `F : FrameModel M` reuses the existing universal-frame representation of
  isomorphisms O_U ≅ f^*M on every B-scheme. The witness
  `e : F.space ≅ Over.mk p.left` has the requested orientation over B.
- The quantified equation for `x,y,z` asserts that multiplication of an
  E-point x by `z ≫ j` corresponds to multiplying its frame by the Laurent
  coordinate of z. Because j and the multiplication are already specified,
  this is exactly `[g,w] ↦ [g,zw]` on quotient representatives.
- The witness `a`, equation `ha` and equation `g ≫ a = bracket rep g 1`
  specify the canonical B-map `g ↦ [g,1]` on every test scheme.
  `sectionOver q.hom.hom p a ha` is exactly this map regarded over B.
- The witness `sigma` is an actual frame O_G ≅ q^*M. Its equality with
  `F.at (sectionOver q.hom.hom p a ha ≫ e.inv)` ties it to the canonical map
  and universal frame, rather than choosing an arbitrary trivialization.
- The final quantified equation asserts the positive character sign on all
  B-test schemes: when h=g i(t), the frame evaluated at h is the frame at g
  multiplied by the Laurent coordinate of chi(t), without inversion.
  These are exactly the pullbacks of the specified sigma by naturality of
  FrameModel.at and the normalized tensor-pullback comparisons.
  The test scheme G×_kT gives the node's displayed equality; conversely that
  scheme-level equality pulls back to this arbitrary-test formulation.

Dependency declarations reused:

- Mathlib: `Field`; `CategoryTheory.GrpObj`, `Grp`, `IsCommMonObj`, `IsMonHom`,
  and group structures on Hom, as recorded for def-sc-group-scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.multiplicative`
  and its existing `multiplicativeGroup` structure.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, and
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  its diagonal and `IsPullback`, plus actual cartesian products in `Over`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  normalized `tensorPullbackSectionComp`; these underlie the recorded frame model.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.splitTorus`.
- `Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`: `FrameModel`, `FrameModel.at`,
  `pullFrame`, `unitComparison`, and `Good`. These plain definitions are now owned
  by `def-sfb-split-torus-frame-model`, cited in stmt_deps.
  The unchanged theorem node is retained in proof_deps.
- Standard categorical constructions: `coequalizer`, `coequalizer.π`, `sheafify`,
  `toSheafify`, `uliftYoneda`, and `Presheaf.IsLocallySurjective`.

Edge cases checked before writing: r=0 gives T=1 and E=G×G_m; the trivial
character gives the trivial G_m torsor over B; G=T and B=Spec k gives G_m,
including the inseparable character t↦t^p in characteristic p. No algebraic
closedness, perfectness, nonzero rank, or connectedness assumption is introduced.
Nonreduced tests remain in the full big fppf site. Empty test schemes are included;
the input group schemes themselves have identity sections over the nonempty field.
The sign follows directly from `(g,chi(t))·t=(g i(t),1)` and is positive.

Sources opened: groupoids.tex at remark-fun-with-torsors (Tag 049C), including
its affine-group representability assertion; descent.tex at
proposition-fpqc-descent-quasi-coherent (Tag 023T). The former is only a source
for affine torsor representability, as the node explicitly acknowledges; the
contracted-product and sign calculations are agent-extracted parts of the node.
The existing frame-module source and full theorem docstring were read.

Searches made:

- msearch.py LeanFinder: “Character pushout of a split torus extension of
  commutative group schemes is represented by an equivariant invertible module
  frame torsor”. Eight hits, including CharacterModule and CommRing.Pic.functor;
  none constructs this represented quotient extension or equivariant frame line.
- msearch.py Loogle: `"QuotientGroup", "map"`. Twelve hits, concerning abstract
  quotient groups and subgroup images; no scheme quotient/frame statement.
- msearch.py LeanSearch: “The fppf sheaf quotient of a commutative group extension
  by a split torus character is a group scheme and a line bundle frame torsor”.
  Eight hits, all abstract GroupExtension splittings; no match to this statement.
- msearch.py grep: `(contracted|characterPushout|character_pushout)` in Mathlib.
  Two irrelevant separable-polynomial contraction hits.
- rg over lean/WeilConjectures and lean/Sheaf for pushout/contracted and
  torus/character: only unrelated logarithmic-characteristic pushouts.
  Direct node-id search in WeilConjectures: no hit.
- rg for splitTorus, frameFunctor and frame/torsor combinations located the
  already landed SplitTorusTorsorFrameGeometry and ToriMultiplicativeType modules,
  which are reused after reading their complete interfaces.

No STATEMENT-DISPUTED issue or mathematical statement correction.
The H2 ownership repair adds the definition node described below.
The six-step natural-language proof is included in the theorem docstring.

Available proof dependencies are imported with plain `import`: the upstream
FormallySmooth, SiteSheafificationSectionsLocal and SmoothFiber modules.
The frame-geometry theorem is a proof dependency. Its plain frame definitions
are a statement dependency through the new owning definition node, rather than
through a theorem whose conclusion is not used by those definitions.
Mathlib proof dependencies are supplied by the existing public imports.
The smooth-affine torsor representability node has no recorded module, so there
is no import to add for it; it is a proof dependency, not an unstated notion
needed to type this statement.

Validation: the complete file compiled in both sandbox and library mode through
scompile.py with only the expected theorem-sorry warning. An earlier dependent
record formulation hit the 60-second limit; expressing the same conclusion as
an existential proposition avoided generated projection/recursor reductions.
No timeout increase or limit override is used in the delivered module.


## New nodes

`def-sfb-split-torus-frame-model` registers the five existing declarations
`SplitTorusFrames.unitComparison`, `pullFrame`, `FrameModel`, `FrameModel.at`,
and `Good` in `Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`, using
`existing: true`. Its main signature is the verbatim `structure FrameModel`
signature in that landed source. No Lean file is copied or moved and the landed
frame-geometry theorem record is retained. The source is the frame specialization
of Stacks 01OB, canonical module pullback 0096/0097, and the smooth, closed
diagonal and finite-type definitions 01V4/01KU/01T0. The new node defines a
frame model for any module without asserting existence for a noninvertible
module. The structure contains a universal frame and bijectivity on every
S-scheme; its evaluation is actual normalized tensor pullback. Good expands
exactly to Smooth, closed diagonal, LocallyOfFiniteType and QuasiCompact.

The three msearch queries and exact logged results are recorded in the new node.
LeanSearch returned eight pullback/sheaf results, LeanFinder eight affine-space
and pullback results, and Mathlib grep for FrameModel/pullFrame/unitComparison
returned no hits. Source rg locates exactly the landed five names. DAG rg and
`blueprint_refs.py search frame` found the frame-geometry theorem but no owning
definition node. Thus this registers an existing notion rather than introducing
a duplicate. `blueprint_refs.py ancestor` reports `None`, retained as JSON null;
via is the item followed by its existing via chain.

## Second reading by Q18

Self-check for the repair, with the item, new node and both Lean modules open:
H2 was a dependency-ownership error. FrameModel and Good occur in Geometry,
FrameModel.at in its frame and equivariance clauses, and pullFrame and
unitComparison implement the evaluated universal frame. None is obtained from
the frame-geometry theorem. The item's stmt_deps therefore replaces that
theorem with def-sfb-split-torus-frame-model; proof_deps still contains the
theorem. The existing FrameModel definition is reused verbatim and its five
declarations are listed on the new node. The theorem node is not edited.

Re-reading the unchanged theorem against the item: the field, commutative
group objects, smoothness, closed diagonals, locally finite type plus
quasi-compactness, arbitrary nonnegative rank, kernel pullback, fppf local
surjectivity and homomorphic character are exactly the stated hypotheses.
Geometry retains the specific action quotient and sheafification, represented
commutative smooth separated finite-type group with induced multiplication,
the specified kernel and locally surjective exact sequence, invertible module,
universal frame model, scalar equivariance and canonical frame's positive
character equation on every test scheme. Rank zero, trivial characters,
nonreduced and empty tests remain included. No signature, construction,
universe or mathematical assertion changed. The advisory existential sigma
clause is retained as an explicit name for the canonical evaluated frame.

The initial saved-packet dry run passed at 582ba4bc4b2; this did not discharge
the independent H2 review, so the ownership repair above is included before
recompilation and the final dry run and push.

Repair validation: scompile.py compiled the retained item cleanly in sandbox
and library modes (16.8 s and 9.0 s). The repaired-packet dry run requested
the new-node schema field import_flags; it is now present as the empty list,
matching existing stage-2 definition nodes. No mathematical or Lean change.
