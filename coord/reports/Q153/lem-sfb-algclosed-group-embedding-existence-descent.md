## Worker report

The module `Sheaf.AlgebraicGeometry.AlgClosedGroupEmbeddingExistenceDescent` states
`AlgebraicGeometry.exists_closed_group_embedding_iff_of_isAlgClosed`. Its only proof is
`sorry`; it introduces no definitions or additional theorems. The item's JSON changes only
in `lean`. The source statement needs no correction and is not disputed.

Clause-by-clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- An arbitrary field extension is `{L : Type u} [Field L] [Algebra F L]`.
  There is no algebraicity, finiteness, separability or algebraic closedness assumption on L.
- The F-group schemes are `G H : Grp (Over (Spec (.of F)))`. Each underlying over-object
  has the existing `GrpObj` structure, comprising multiplication, identity, inverse and laws.
  Bundling does not restrict the group schemes: `Grp.mk` bundles any such structure.
- Affineness is `[IsAffine G.X.left] [IsAffine H.X.left]`.
- Finite type is `[LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]`, together
  with the quasi-compactness already inferred from affineness. In Mathlib's Affine.lean,
  `isAffineHom_of_isAffine` (181) applies to maps between affine schemes, and the instance
  at 58 makes an affine morphism quasi-compact. Spec F is affine. Thus separate
  `QuasiCompact` binders would be redundant hypotheses, and no finite-type clause is lost.
- A homomorphism over F is `j : G ⟶ H`. It contains an over-scheme morphism
  `j.hom.hom` and the existing `IsMonHom` compatibility. This includes the unit equation;
  for group objects it is equivalent to the node's multiplication-only formulation,
  since a multiplication-preserving map sends identity to the identity (an idempotent
  element of a group is the identity). No commutativity is imposed.
- Its being a closed immersion is exactly `IsClosedImmersion j.hom.hom.left`.
- Put `b = Spec.map (CommRingCat.ofHom (algebraMap F L))`. The two scalar extensions are
  `(Over.pullback b).mapGrp.obj G` and `(Over.pullback b).mapGrp.obj H`. Mathlib's
  `Functor.mapGrp` uses the canonical group law induced by the monoidal pullback functor,
  rather than an arbitrary group structure on the pullback scheme. Its underlying
  over-object is `(Over.pullback b).obj G.X`, respectively H.X. These are the fibre
  products and second projections specified by def-pc-base-change.
- `∃ j' : ... ⟶ ..., IsClosedImmersion j'.hom.hom.left` is exactly existence of an
  L-group homomorphism which is a closed immersion.
- The connective is `↔`. The two existential variables are independent: no equation
  requires j' to be the extension of j. There are no smoothness, reducedness or
  connectedness assumptions.
- All variables and universe parameters are explicitly bound. A common arbitrary
  universe u accommodates F, L and the two schemes; choosing a common universe does
  not impose any cardinality, algebraicity or relative-size constraint on L/F.

Statement dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic,
  is the algebraic-closedness component of the recorded AlgebraicClosure interface;
  the node here does not ask to choose an algebraic closure of another field.
- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs, with two `Field` instances.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, `CategoryTheory.Grp` and
  `CategoryTheory.IsMonHom`, Mathlib.CategoryTheory.Monoidal.Grp and its Mon import.
  Read the full group-scheme convention in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, and the current blueprint
  `literature/blueprint/latest/blueprint/sec-abelian-varieties/sk-def-av-group-scheme/def-sc-group-scheme.md`.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `AlgebraicGeometry.QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact (inferred as explained above).
- def-pc-base-change: imported WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
  its documented scheme convention uses `CategoryTheory.Over.pullback`, which is
  precisely the construction used here, lifted by `CategoryTheory.Functor.mapGrp`.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.

Proof-only imports retain the recorded proof plan: AffineFiniteTypeAlgebra
(`affine_finiteType_algebra_of_field`), ColimitCategoryFpAlgebras
(`RingHom.exists_map_of_finitePresentation_colimit`), Noetherian.Defs
(`IsNoetherianRing`), FinitePresentation (`Algebra.FinitePresentation.of_finiteType`),
Pullbacks (`pullbackSpecIso`), FiniteType (`RingHom.FiniteType`), Spectrum.Maximal.Basic
(nonempty maximal spectrum), and AlgClosed.Basic (`residueFieldIsoBase` and
`SpecMap_residueFieldIsoBase_inv`). Closed-immersion base-change stability and Spec
are already supplied by public statement imports. All thirteen proof dependencies
are covered, without inventing prerequisites. The theorem docstring records all six
proof steps, the directed-union verification, tensor injectivity, finite witnesses
and specialization. Read the actual Stacks 01ZM and 00FV statements in limits.tex
and algebra.tex, respectively.

Edge cases checked before writing: L = F makes the two existence assertions equivalent
by canonical identity base change; a transcendental extension is admitted. The trivial
group (zero algebra generators) is included and the finite-witness proof still works.
Positive characteristic and nonreduced groups such as alpha_p or mu_p are included:
the statement and proof use scheme morphisms and tensor equations, not geometric-point
injections. Disconnected and noncommutative affine groups are admitted. An empty group
scheme over a field cannot have an identity section, so no permissible group is excluded
by its absence. The forward direction works without algebraic closedness; that assumption
is needed for specialization in the reverse direction.

Searches actually run (2026-10-24):

- msearch.py leanfinder: "Existence of a closed group scheme embedding over an
  algebraically closed field descends along any field extension". Eight results:
  IsAlgClosed.lift_def, IsAlgClosed.lift, isField_of_universallyClosed,
  Field.embEquivOfIsAlgClosed, instIsClosedImmersionLiftCoborder,
  finite_appTop_of_universallyClosed,
  instIsClosedImmersionOfSubsingletonCarrierCarrierCommRingCatOfIsOver,
  PreGaloisCategory.autEmbedding_isClosedEmbedding. None gives existence descent
  of a group-scheme closed immersion.
- msearch.py loogle: `"IsAlgClosed", "IsClosedImmersion"`: zero hits.
- msearch.py grep: `[Aa]lg[Cc]losed.*[Cc]losedImmersion|[Cc]losedImmersion.*[Aa]lg[Cc]losed`
  in AlgebraicGeometry: zero hits.
- msearch.py leansearch: "Existence of a closed embedding between affine finite type
  group schemes descends to an algebraically closed base field". Eight results,
  all existing closed-immersion predicates, constructors, consequences and stability
  under base change; none is the existence equivalence here.
- rg in lean/WeilConjectures and lean/Sheaf for
  `exists.*[Cc]losed.*[Ii]mmersion|embedding.*[Dd]escent|embedding.*isAlgClosed|IsAlgClosed.*embedding`:
  various spreading, compactification and closed-complement results, none this statement.
- grep for the exact item ID in lean/WeilConjectures: zero hits.
- rg in Mathlib, lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `exists_closed_group_embedding_iff_of_isAlgClosed|AlgClosedGroupEmbeddingExistenceDescent`:
  zero hits. A narrower group-scheme search also found no such statement.

Validation: scompile.py compiled the final module successfully both as the sandbox probe
and under its actual library module name (5.1 s and 3.3 s); no errors or warnings.
An initial projection typo `j.hom.left` was corrected to `j.hom.hom.left` after reading
the bundled group and monoid hom signatures; the final statement compiles cleanly.

## Second reading by Q153

The dispatcher explicitly forbids starting other agents; this section records a final
self-audit, not a claim of an independent worker review. The maintainer's independent
review remains the independent second reading prescribed in the assignment.

Reopened the node and final module and compared every clause listed above. In particular,
checked the two nested hom projections against Grp/Mon's actual signatures, confirmed
that mapGrp carries the group law rather than just base-changing underlying schemes,
checked finite type against the inferred quasi-compactness, and confirmed that the two
existential morphisms are not tied by an equality. No statement change, dependency repair,
new notion or remaining mismatch was found. The only elaboration repair was the nested
hom projection described above.
