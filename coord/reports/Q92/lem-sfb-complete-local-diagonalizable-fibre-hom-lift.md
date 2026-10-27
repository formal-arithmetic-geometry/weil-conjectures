## Worker report

Stage 2, Q92, item `lem-sfb-complete-local-diagonalizable-fibre-hom-lift`.
The module `Sheaf.AlgebraicGeometry.CompleteLocalDiagonalizableFibreHomLift`
states `AlgebraicGeometry.completeLocal_diagonalizable_fibre_hom_lift`, with
one named theorem and its sole proof `sorry`. It adds no definition and changes
only the item's `lean` record. The complete seven-step accepted proof is in the
theorem docstring. No statement correction or disputed statement is necessary.

Source read: Conrad, *Reductive group schemes*, Theorem B.3.2(2), printed
pp.288--290, at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf.
The online theorem and its proof explicitly give the Hom bijection and the
open-and-closed immersion conclusion for a flat affine finite-type target.
Our source H = D_A(M) is already split, hence satisfies the source's temporary
finite-etale splitting assumption by the identity cover. No smoothness is added.

Hypotheses and clauses, in order:

- `(A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]` is the
  commutative Noetherian local base. Mathlib's local ring is nontrivial, as is
  required to have the residue field in the node.
- `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]` says that the canonical
  map to the maximal-ideal-adic completion is bijective. This is precisely the
  recorded completion dependency's companion notion, not merely precompleteness.
  Starting the inverse system at zero rather than one only inserts the zero
  ring quotient and does not change the completion.
- `IsLocalRing.ResidueField A` is definitionally `A ⧸ maximalIdeal A`, and
  `IsLocalRing.residue A` is the quotient homomorphism. `Spec (.of A)` is S.
- `G : Grp (Over (Spec (.of A)))` is an S-group scheme, with multiplication,
  unit and inverse; categorical morphisms in this category are precisely
  group-scheme homomorphisms. No commutative-group-object instance is required.
- `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [Flat G.X.hom]` express
  G = Spec B for an A-algebra B that is finitely generated and A-flat.
  B may be recovered canonically as the global sections of the affine G;
  no separately chosen presentation of its coordinate ring is needed.
  On affine source and target, the definitions of `LocallyOfFiniteType` and
  `Flat` apply to the top affine opens and say exactly that the coordinate map
  has finite type and is flat. Conversely these coordinate properties imply
  the displayed scheme properties. An affine source is quasi-compact, so
  locally finite type here is finite type, not a weakening. These properties
  include neither smoothness nor commutativity.
- Every occurrence of `(Over.pullback (Spec.map (CommRingCat.ofHom
  (IsLocalRing.residue A)))).mapGrp.obj G` is G_k, using the actual chosen
  scheme fibre product and its induced group law. The `.mapGrp.map` function
  is the corresponding canonical restriction on group homomorphisms.
- `hG` spells out the node's multiplicative-type hypothesis directly: its
  `I`, `R`, and `f` give affine schemes Spec(R i) over Spec k; membership of
  `Presieve.ofArrows ... f` in `Scheme.fppfPrecoverage` is exactly joint
  surjectivity, flatness and local finite presentation of this family.
  For every member, the existential `N`, `AddCommGroup N`, `AddGroup.FG N`
  and `Nonempty (... ≅ ringDiagonalizableGroup (R i) N)` give the specified
  diagonalization as a group scheme, retaining every Hopf operation.
  Taking affine covering members loses no case: refine any supplied fppf
  diagonalizing cover by affine opens, on which the same groups still
  diagonalize. This is the recorded `lem-pc-fppf-affine-refinement`.
  Conversely the displayed affine cover is itself an fppf cover. A finite
  refinement of the affine base exists, so `I : Type u` imposes no size
  restriction on the existence of a diagonalizing cover.
- `(M : Type u) [AddCommGroup M] [AddGroup.FG M]` ranges over the finitely
  generated abelian character groups, and `ringDiagonalizableGroup A M`
  is exactly Spec A[M] with the recorded group-algebra Hopf structure.
- `Function.Bijective (...mapGrp.map (X := ringDiagonalizableGroup A M)
  (Y := G))` is the required bijection: its codomain is the Hom set from
  the actual special fibre of D_A(M) to G_k. This is the chosen-pullback
  presentation of Hom(D_k(M),G_k): the affine fibre-product formula identifies
  its source coordinate algebra with k tensor_A A[M] = k[M] by
  r tensor e_m ↦ r e_m, preserving coproduct, counit and antipode.
  The statement uses the actual pullback source, as Conrad's H_0 does;
  it does not posit an arbitrary comparison isomorphism or an arbitrary map.
- The second conjunct quantifies over every `j : ringDiagonalizableGroup A M
  ⟶ G` and asserts `IsOpenImmersion j.hom.hom.left ∧
  IsClosedImmersion j.hom.hom.left` when its pulled-back group homomorphism
  is `IsIso`. The first conjunct supplies, for each isomorphism j_0, exactly
  one lift j; the second supplies the two requested properties of that lift.
  Equivalently, every lift of j_0 has them. This combines the clauses without
  constructing a choice of inverse to the bijection.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, and its recorded
  companion `IsAdicComplete` (the latter is used in the hypothesis).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`,
  also exported by the geometric statement dependencies.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with `Module.Flat` and
  `RingHom.flat_algebraMap_iff`; its affine-geometric rendering used here is
  `AlgebraicGeometry.Flat` from `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  base-change bundle, including `baseChange_morphism_projections`. As its
  node's lean.note directs, scheme and morphism base change use the existing
  `Over.pullback`, not the bundle's module-only `moduleBaseChange`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; the family's membership uses the former exactly.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup` (read also its recorded
  companion `ringDiagonalizableGroupMap`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- Auxiliary Mathlib interfaces already provided, not redefined:
  `Functor.mapGrp`, `Grp`, `Over.pullback` and its cartesian monoidal instance,
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`, `AddGroup.FG`.

All stated proof dependencies are imported, privately when only needed for the
proof. This includes the affine fibre-product, finite presentation, flat base
change, affine fppf refinement, scheme gluing, fppf/fpqc and representable
descent, flat closed-family ideal sequence, finite-type Noetherianity,
Nakayama, ideal subscheme and basic-open interfaces. The following proof
prerequisites have no recorded Lean declaration at this delivery's reading,
so there is not yet a module to import: `lem-sfb-nilpotent-flat-multiplicative-deformation`,
`lem-sfb-relative-diagonalizable-character-duality`,
`lem-sfb-adic-diagonalizable-hom-effectivity`,
`lem-sfb-local-torus-subgroup-special-trivial`,
`lem-sfb-affine-multiplicative-type-monomorphism-closed`, and
`lem-sfb-flat-subgroup-identity-neighbourhood-open`.
Their use is retained in the proof docstring; the statement needs no declaration
from any of them. There is no dependency repair and no new node.

Edge cases checked before writing:

- M = 0 gives the trivial source; the map on Hom sets then has the expected
  single identity-valued morphism on both sides. If G_k is trivial, the identity
  section is asserted to be open and closed, as in the source theorem.
- Torsion M, including p-torsion in residue characteristic p, remains allowed:
  `AddGroup.FG` does not imply torsion-freeness, and the Hopf group algebra
  does not require reducedness or smoothness.
- A field base has maximal ideal zero, so its residue pullback is an
  isomorphism and the asserted bijection reduces to transport along it.
- Artinian and nonreduced complete local rings are covered.
- Noncommutative and nonsmooth targets satisfy precisely the displayed
  group-object, affine, flat and finite-type conditions; no extra instance
  restricts them. The second conjunct is not asserted for a nonisomorphic
  special-fibre homomorphism.
- Empty covering families cannot cover the nonempty spectrum of the residue
  field: membership in `fppfPrecoverage` really requires joint surjectivity.
  No artificial `Nonempty I` or other extra covering hypothesis was added.
- All rings, character groups and schemes have the same object universe u.
  This is the existing ringDiagonalizableGroup interface and excludes no
  finitely generated character group up to isomorphism (all are countable).
  Covering rings have the universe of the schemes, not an independent smaller
  universe; finite affine refinements fit the chosen index universe.

Searches made (all service queries through the prescribed msearch.py):

1. LeanFinder, `Homomorphisms from diagonalizable group schemes lift uniquely
   over complete noetherian local rings with multiplicative type special fibre`:
   eight hits, on valuative criteria, affine-transition-limit morphisms and
   formally unramified ring-map lifting; no match for either conclusion.
2. Loogle, `"Grp", "map"`: twelve hits, all on ordinary bundled algebraic group
   categories (ULift and forgetful maps), not the group-scheme lifting theorem.
3. Grep service, `diagonali[sz]able|MultiplicativeType|multiplicative.type` in
   `Mathlib/AlgebraicGeometry`: zero hits.
4. LeanSearch, `A homomorphism from a diagonalizable group scheme uniquely lifts
   from the special fibre over a complete local ring`: eight hits, on
   `IsAdicComplete.liftAlgHom`, ordinary formally smooth ring lifting,
   residue-field maps and dual numbers; no group-scheme match.
5. Local rg of WeilConjectures and Sheaf for diagonalizable/multiplicative-type
   constructions and complete-local Hom lifts, plus item-id search in
   WeilConjectures, Sheaf and `dag/lean_names_upstream.json`: the exact item
   has no declaration. `CompleteLocalSplitTorusHomLift` is a different theorem:
   its target is smooth, its source is a torus, and lifting there is only an
   existence assertion, not this multiplicative-special-fibre bijection.
6. Read the existing `ToriMultiplicativeType` predicate and the definition
   nodes concerning multiplicative type. That field-only algebraic-closure
   predicate uses a closed embedding into a split torus; the present node
   explicitly gives fppf local diagonalizations, which are written inline
   using the existing fppf and diagonalizable-group definitions. No duplicate
   named predicate is introduced.

Validation: scompile.py compiled the sandbox and library-module presentations
cleanly on the live server (2.8 s and 2.9 s). Every universe and variable is
explicit; both autoImplicit and relaxedAutoImplicit are disabled. No theorem
is proved, no local notation or private helper is introduced, and no data
is defined by sorry.

## Second reading by Q92

Separate rereading of the node, source theorem and the delivered signature by
the assigned worker. No additional agents were started, as the dispatch brief
requires; the maintainer supplies the independent delivery review.

Checked each binder against the node again: the ring is local, Noetherian,
and complete; the target is an affine flat finite-type group; its residue
fibre has an actual fppf diagonalizing cover; the source character group is
finitely generated abelian with torsion permitted. The type of the function
in the first conjunct has source Hom(D_A(M),G) and target Hom(H_k,G_k), and
its body is the existing pullback functor's map. H_k is precisely the fibre
of that same D_A(M), canonically D_k(M), not an unrelated source object.
For the second conjunct, `IsIso` is a group-scheme isomorphism on the fibre
and the immersion predicates are applied to the underlying scheme morphism
of the original j. Bijectivity already gives existence and uniqueness for
each j_0, so quantification over j loses none of the isomorphism-lifting clause.

The only presentational differences are intrinsic affine-scheme properties
instead of naming a coordinate algebra B, affine refinement of the fppf
cover, and chosen-pullback presentation of D_k(M); the preceding clause audit
explains each equivalence. No hypothesis or conclusion has changed. No
mathematical mismatch was found; only an extra leading space in a docstring
line was removed after the initial compile. The node has only a lean delta.
