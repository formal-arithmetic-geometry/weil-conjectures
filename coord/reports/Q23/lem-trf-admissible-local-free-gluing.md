## Worker report

Stage 2, Q23, 2026-10-23. The accepted eight-step stage-1 split is preserved.
This repairs the maintainer return for immutable head d5fa17d40ddd (H13/H4).
The initial required dry run of the saved packet passed as ce2dab5f7fd, but that
mechanical result does not repair the independent review finding. The repair below
implements the maintainer's explicitly permitted option (b).

Delivered modules:
- Sheaf.AlgebraicGeometry.AdmissibleLocalFreeGluing states
  AlgebraicGeometry.Scheme.Modules.exists_admissibleBlowup_localFree_gluing.
  Its AdmissibleBlowupDatum helper packages the existing IsAdmissible centre with
  a specified morphism and identification; it is listed in this item's lean.declarations.
  Its three helper definitions construct transport along the specified blowup
  identification, the canonical open fibre-product inclusion, and the comparison
  induced by the refinement map. Each uses real data and the existing pullback and
  strict transform definitions. No independent mathematical notion is duplicated.
There is no dependency module or dependency-record change in this delivery.
The live def-nagata-admissible-blowup record remains byte-identical, pointing to
AlgebraicGeometry.IsAdmissible in WeilConjectures.Blowup.AdmissibleBlowup.

Hypothesis-by-hypothesis correspondence:
- Schemes S and X are `{X S : Scheme.{u}}`. Their point and coefficient universes
  agree with the dependency's module strict transform, not with a new size assumption.
- S quasi-compact and quasi-separated is `[CompactSpace S] [QuasiSeparatedSpace S]`.
- The quasi-compact open U is `(U : S.Opens) (hU : IsCompact (U : Set S))`.
- The flat morphism is `(f : X ⟶ S) [Flat f]`; no quasi-compactness, finite
  presentation, affineness or other property of f is assumed.
- The finite-type quasi-coherent module is `(F : X.Modules) [F.IsQuasicoherent]
  [F.IsFiniteType]`, the two factors in the recorded IsQuasiCoherentFiniteType.
- The finite family of quasi-compact opens is `{J : Type v} [Finite J]`,
  `(W : J → S.Opens)` and `hW`. `hcover : iSup W = ⊤` is exactly the cover condition.
  J has its own explicit universe; no enumeration, inhabitedness or decidable
  equality hypothesis is imposed.
- `Tj`, `bj` give the actual local morphisms T_j to W_j. `D j` is their specified
  admissible datum relative to `(W j).ι ⁻¹ᵁ U`, the open U intersect W_j on W_j.
  Its compactness field records the quasi-compact preserved open from the datum
  formulation; here it also follows from qcqs S and the quasi-compact opens U and W_j.
- `Vj j` is an open of the iterated fibre product of X_Wj and T_j over W_j.
  `hsurj j` says its composite map to T_j is surjective.
- `hfree j` says the local strict transform restricted to V_j is finite locally free.
  `F.restrict (f ⁻¹ᵁ W j).ι` is the restriction of F to X_Wj. The helper
  admissibleGluingTransform takes the strict transform for the retained centre
  D.center.I and pulls it back along the map induced by D.iso. Thus it is the same
  strict transform on the specified T_j rather than a substitute blowup.

Conclusion-by-conclusion correspondence:
- `∃ B : IsAdmissible S U` supplies the global finite-type centre, disjoint from U;
  take T = B.I.blowup and b = B.I.blowupMap. This is a normal form for the existential
  blowup, with its specified identification the identity. The input hU supplies
  quasi-compactness of its preserved open, so this gives the full admissible datum.
- `∃ c`, `∃ hc` give each c_j : T times_S W_j to T_j and its equation over W_j.
- The first universal conjunct supplies `Nonempty (AdmissibleBlowupDatum ... (c j))`
  relative to the inverse image in T_j of U intersect W_j. This retains the
  refinement centre and its actual blowup isomorphism, not just a factorization.
  Nonempty here expresses existence of the datum in the theorem's conclusion;
  no construction is chosen from it in a definition.
- The second universal conjunct is an isomorphism on the inverse image of V_j.
  Its left side pulls F^b back along that open's inclusion in the global family;
  its right side is the ordinary tensorPullback along the restricted comparison
  map to V_j of F_j restricted to V_j. It uses the recorded ordinary pullback,
  and makes no extra quotient-compatibility assertion absent from the statement.
  Pullback along the open inclusion is canonically restriction; this permits both
  sides to live on the exact same iterated fibre product, without arbitrary casts.
- `∃ V` gives an open in X times_S T. The displayed equality of underlying sets
  says exactly V is the union of the images of those inverse-image opens under
  admissibleGluingInclusion. The equality, rather than merely containment, is kept.
- `Surjective (V.ι ≫ pullback.snd ...)` is surjectivity over T, not over S.
- The final IsFiniteLocallyFree says F^b restricted to this V is finite locally free.
  All such predicates have explicit .{u,u,u} parameters; rank may vary and rank zero
  is allowed. There is no fixed-rank or positive-rank assumption.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom;
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, fst, snd,
  lift and map. Mathlib supplies HasPullbacks Scheme. These form all fibre products.
- def-weil-pbc-scheme-conventions is explicitly only a convention node; its recorded
  interpretations CompactSpace, QuasiSeparatedSpace and Surjective are used inline.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat and its
  stalkwise interpretation. The original source definition was read.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  Scheme.Modules.IsQuasiCoherentFiniteType, whose two constituent predicates are
  used as the original typeclass binders required by moduleStrictTransform.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators:
  SheafOfModules.IsFiniteType, locally finitely generated, as recorded by
  def-weil-pbc-module-finite-type-presentation.
- WeilConjectures.Blowup.AdmissibleBlowup: IsAdmissible, re-used as the centre
  field of the datum. Its original full structure signature and docstring were read.
- Sheaf.AlgebraicGeometry.ModuleStrictTransform: moduleStrictTransform,
  moduleStrictTransformOpen, moduleStrictTransformRestriction and
  moduleStrictTransformKernel. The actual supported-section kernel quotient is used.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: tensorPullback and the
  section-normalized tensorPullbackSectionAdjunction/Comp/Id interface, read in full.
  Only its existing tensor functor is needed for the statement.
- WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule:
  Scheme.IdealSheafData.isFiniteType_toModules_sheaf bridges the datum's finite-type
  ideal to moduleStrictTransform's required ideal-module instance, without a new axiom.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree:
  SheafOfModules.IsFiniteLocallyFree is the existing variable-rank local finite free
  predicate (its definition and generator data were read).

Proof-dependency imports are retained where the nodes have recorded declarations,
including ModuleStrictTransformFlatPullback, StrictTransformComparisonEpimorphism,
RelativelyFlatModulePullback, the upstream complement, flat-base-change, product and
principalization interfaces, the flat ring-map definition and surjective-base-change
Mathlib file. The two currently unstated proof nodes for iterated exceptional support
and relative-flat Cartier support have no module to import. They are not needed to
write this statement and no postponed extra lemma is hidden in the definitions.
The theorem docstring reproduces the accepted eight-step proof and its prerequisites.

Edge cases read before drafting and checked again against the final signature:
J may be empty, which forces S empty by hcover; the existential unit blowup and empty
V are then allowed. Individual W_j, U, or the blown-up bases may be empty. U = S
forces unit centres locally but still allows the natural identity blowups. Zero and
unit ideals are not excluded, and centre-dependent transforms are retained even when
the underlying blowup morphism is an isomorphism. The zero module and rank-zero free
loci are allowed. No density condition on U, affineness of intersections, compactness
of X or V_j, or global constant rank was added. The result only requires surjectivity
onto the resulting T, so empty blowup components cause no omitted case.

Searches (all msearch invocations were Q23 for this item; actual machine-readable
outputs are retained in searches.jsonl):
- LeanFinder: “A finite admissible common blowup preserves finite locally free strict
  transforms on opens surjective over the base”; eight hits on jointly-surjective
  families, finite/locally quasi-finite morphisms and finite-presentation base change.
  None is the stated module strict-transform gluing theorem.
- Loogle: `"blowup", "Surjective"`; zero hits.
- msearch grep in AlgebraicGeometry: `admissible|moduleStrictTransform|IsLocallyFree`;
  five elliptic-curve admissible-variable-change hits, unrelated to blowups.
- LeanSearch: “A common admissible blowup glues finite locally free loci of strict
  transforms of a module”; freeLocus and general scheme/ringed-space gluing hits.
  None involves a common admissible centre or strict-transform comparison.
- LeanFinder: “Admissible blowup datum with specified morphism and isomorphism to the
  blowup of a finite type ideal”; quotient-scheme and ideal-subscheme/etale hits,
  no datum interface. Direct project search found only the upstream IsAdmissible.
- Read-only rg searches of lean/WeilConjectures and lean/Sheaf for admissible gluing,
  moduleStrictTransform, local-freeness, AdmissibleBlowupDatum and the proposed names;
  read GenericFreeBlowup, ModuleAdmissibleBlowupCalculus and the exact strict-transform
  interfaces. GenericFreeBlowup is a different statement and proof-consumer of this
  result; using it would be circular. Neither it nor TwoOpen/CommonModification says
  this module theorem. The required grep for the exact blueprint id in
  lean/WeilConjectures returned no hit. There is no existing declaration of this item.

Sources opened: flat.tex remark-successive-blowups in full, including the finite
sequence reduction and final paragraph; divisors.tex lemma-strict-transform-flat,
lemma-extend-admissible-blowups and lemma-dominate-admissible-blowups. The formulation
follows their actual retained-centre refinement and local-to-global route. No source
was fetched from the web; all cited text is available locally.

Validation: the repaired single module compiled through the prescribed scompile.py
with exit 0, in both sandbox mode (4.4 s) and library mode (4.3 s), with no warnings
or errors. Earlier elaboration failures were repaired by explicit scheme coercions,
explicit finite-locally-free universes, and projection equation rewrites.
The final right side explicitly pulls back the restricted local module from V_j.
No statement correction, disputed statement, new definition node or open node fault.

## Repair of H13/H4

The live record of def-nagata-admissible-blowup was usable and must not be rebound.
Its original AlgebraicGeometry.IsAdmissible declaration is directly imported and
used for every retained centre and the global B existential. The dependency node
copy and the standalone AdmissibleBlowupDatum module were removed from this packet;
there is no delta to the live dependency record. AdmissibleBlowupDatum is now a
listed helper in the item module, exactly the option (b) authorized in the return.
It packages IsAdmissible with compactness and the specified morphism's blowup
identification; it does not replace or redeclare IsAdmissible. Its source/blueprint
docstring names this item. The theorem signature and all three map/transform helper
bodies are retained from the reviewed delivery.

The advisory about quotient-map compatibility was considered. The node asks for an
isomorphism with ordinary pullback, and the return accepts that clause. The bare
Nonempty isomorphism is therefore retained; the proof docstring still explains the
quotient-compatible construction that proves this existence statement. No extra
compatibility conclusion is added to the statement.

## Second reading by Q23

I re-opened the final node, the single item module and the unchanged live dependency
record and checked each hypothesis and conclusion against the correspondence above.
The explicit instruction for this dispatch forbids starting other agents, so this is
a separate final reading by the assigned worker, not an invented second-worker review.

The maintainer identified the interface repair as a mismatch: IsAdmissible was
usable and the dependency record must remain unchanged. This repair moves the
packaging helper into the item module and lists it under the item, preserving the
existing dependency declaration and every mathematical clause of the theorem. The initial
pullback-isomorphism expression used the unrestricted local transform; although
canonically equivalent, it was rewritten as ordinary pullback of its restriction to
V_j to match the node literally. The explicit set equality retains the union clause.
The global B existential is a chosen blowup normal form, equivalent to the arbitrary
T,b datum in the node; the given hU and identity isomorphism recover the omitted
packaging. All hypotheses bind genuine assumptions, including empty cases and variable
rank. No compile workaround introduces an extra universe equation or size hypothesis.

The final theorem has only sorry as its proof. The helper constructions use the
existing strict transform and projection-determined pullback maps; their proof terms
only establish the defining commutative squares and do not prove independent results.
There is no hollow definition or unrecorded postponed theorem. All variables and
universes are explicit, each helper is listed in lean.declarations, and all
module/declaration docstrings carry the owning node id. The read-only repository
and launcher sources have not been modified and no direct git command was run.
