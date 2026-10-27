## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinTangentRingLiftCriterion` states
`AlgebraicGeometry.ArtinDeformation.isVersal_of_tangent_surjective_of_ring_lifts`.
Its single proof is `sorry`, as required for stage 2. No definition, dependency
interface, node statement, or dependency list is changed.

Hypotheses and clauses, matched individually:

- A commutative Noetherian base ring is `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`.
- The finite type residue field is `{k : Type u} [Field k] [Algebra R k]
  [Algebra.FiniteType R k]`. Finite type here is the algebraic finite type condition,
  equivalent to finite type of its affine structure morphism; it is not an
  assumption that k is a finite R-module.
- The test category is the dependency's `TestCategory R k`. Its objects have marked
  augmentations with maximal kernel, equivalent to the specified residue-field
  isomorphism. Its arrows are local R-maps preserving that marking.
- The category cofibred in groupoids is `F : CofibredGroupoids.{u, v, w} R k`.
  Its coherent transport is the dependency's pseudofunctor.
- The predeformation and (RS) hypotheses are separately `hpre : IsPredeformation F`
  and `hRS : IsRimSchlessinger F`. The former retains terminality of the groupoid
  at k; the latter is the actual fibre-product comparison equivalence.
- The complete Noetherian marked local algebra is `C : CompleteLocalAlgebra R k`;
  completeness, locality, Noetherianity and the specified residue R-isomorphism
  are fields of that structure, not additional implicit assumptions.
- The formal object is `ξ : FormalObject F C`, with the dependency's positive
  truncations and coherent transition isomorphisms.
- The first condition is `htangent : Function.Surjective (...)`. Its domain is
  `LocalMap C (squareZeroTest (R := R) (k := k) k)`, exactly marked local maps
  to k[epsilon]. It sends a to `Quotient.mk _ (evaluate ξ a) : tangentSet F`:
  the isomorphism class of the prescribed formal-object evaluation. The target
  is the dependency's tangent set, not a chosen tangent-vector-space structure.
- The second condition is `hring`: it quantifies over every pair `A B`, every
  arrow `f : B ⟶ A` with `IsSmallExtension f`, every `a : LocalMap C A`, every
  `y : fibre F B`, and every specified `_α : (push F f).obj y ≅ evaluate ξ a`.
  It requires only `∃ b : LocalMap C B, (map f).comp b.hom = a.hom`. It does not
  require an isomorphism between y and the lifted evaluation. The `_α` binder
  deliberately remains even though the returned ring equality does not mention it.
- The conclusion is exactly the dependency's `IsVersal ξ`. Unfolding that
  definition quantifies over ALL surjections, including isomorphisms. It supplies
  b, its lifting equality hab, and β : y ≅ evaluate ξ b, with the equation
  `(push F f).map β.hom ≫ (evaluationRestriction ξ f a b hab).hom = α.hom`.
  Thus the specified isomorphism, with the dependency's canonical restriction
  comparison, is preserved exactly.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely
  generated), provided publicly through the deformation-test module.
- `Mathlib.Algebra.Field.Defs`: `Field`, provided transitively.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, provided publicly through
  the deformation-test module. Also read the recorded scheme predicates
  `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in the corresponding QuasiCompact module.
  Those describe the same finite type hypothesis on affine structure morphisms;
  no scheme-valued replacement is needed in this ring statement.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`: `TestCategory`,
  `CofibredGroupoids`, `IsPredeformation`, `IsRimSchlessinger`,
  `CompleteLocalAlgebra`, `FormalObject`, `LocalMap`, `squareZeroTest`,
  `tangentSet`, `evaluate`, `IsSmallExtension`, `fibre`, `push`, `map`, and
  `IsVersal`. The complete module, including evaluationRestriction, was read.
- Proof-only import `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` supplies the
  recorded Mathlib match
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing` for
  lem-weil-pbc-noetherian-local-quotient-artinian-local.
- Proof dependency lem-sfb-artin-local-test-algebra has no Lean record or Mathlib
  match at this delivery's base. There is consequently no module to import for
  that dependency yet. It is retained in proof_deps and named in the proof
  docstring; it is not needed to formulate this statement.

Source and proof: read `literature/stacks-project/formal-defos.tex`,
lemma-versal-criterion (Tag 06IU), including its sufficient-direction proof,
and lemma-RS-implies-S1-S2 (Tag 06J7). The node uses the stronger assumed (RS)
directly, which keeps the prescribed gluing isomorphism. The declaration docstring
records all five proof steps: reduction to small extensions; gluing over B×_A B;
the difference map and tangent surjectivity; passage to a common Artinian
truncation and second gluing; correction using full faithfulness with identity
component, followed by composition.

Edge cases checked before writing:

- A zero kernel is not a small extension (the dependency requires nonzero
  one-dimensional kernel). Isomorphisms are nevertheless included in IsVersal;
  the proof's zero-factor case transports along the inverse.
- The least positive truncation exists even when C or a test algebra is a field.
  The dependency indexes positive powers by n+1, so no C/m^0 value is imposed.
- The dual-number algebra is the actual square-zero extension k[k]; it exists in
  every characteristic, including characteristic 2. No division by 2 occurs.
- No finite-dimensionality assumption on T F, no smoothness assumption on C, and
  no global ring-lifting assumption have been added. Ring lifts are required only
  when the specified compatible object and isomorphism exist.
- Residue fields are nonzero because of Field k. Thus a zero test ring or zero
  complete ring cannot acquire an impossible residue marking.
- Test rings and C use the dependency's common arbitrary universe u, with residue
  field and base also in u. Independent universes v and w for groupoid morphisms
  and objects remain free; the test quantifier is not in a smaller independent
  universe. No extra equality of fibre universes is imposed.

Searches (2026-10-24; msearch.py, group Q127, item as assigned):

- leanfinder: "A formal deformation object is versal if its tangent map is
  surjective and compatible small extensions admit underlying local algebra
  lifts". Eight results, including Algebra.FormallySmooth,
  Algebra.FormallyEtale and Algebra.FormallySmooth.liftOfSurjective. These
  concern algebras, not the required groupoid isomorphism extension; no match.
- loogle: "Algebra.FormallySmooth, Function.Surjective". Twelve results including
  Algebra.FormallySmooth.iff_comp_surjective and liftOfSurjective; no deformation
  versality criterion.
- leansearch: "A formal deformation is versal when the tangent map is surjective
  and small extension problems admit underlying ring lifts". Eight results on
  formally smooth algebras and cotangent criteria; no match.
- grep via msearch: "IsVersal|IsRimSchlessinger|tangentSet" in Mathlib. Five
  sphere-tangent-set hits, no matching deformation declarations.
- rg in lean/WeilConjectures and lean/Sheaf for tangent/versal, ring lifts,
  IsVersal, IsRimSchlessinger and tangentSet; inspected the existing deformation
  module and its tangent-tensor consumer. They define the notions but do not
  state this criterion. The other StackVersal/ProperCurve notions concern
  different categories and were not substituted.
- grep for the exact item id in lean/WeilConjectures: no result. rg for
  isVersal_of_tangent in the project and dag/lean_names_upstream.json: no result.

No statement dispute, missing statement notion, or source correction was found.
The assigned module compiled cleanly with scompile.py in both sandbox and
library-module modes (3.3 seconds and 2.8 seconds); no warnings were printed.

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
