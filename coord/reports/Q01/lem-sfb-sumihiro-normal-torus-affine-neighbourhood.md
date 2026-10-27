## Worker report

This stage-2 delivery states `AlgebraicGeometry.exists_sumihiro_normal_torus_affine_neighbourhood`
in `Sheaf.AlgebraicGeometry.SumihiroNormalTorusAffineNeighbourhood`. Its only proof is `sorry`.
There are no new definitions, dependency replacements, or statement corrections.
The item's accepted natural-language statement, proof, and proof dependencies are unchanged.
Its statement dependencies gain the already-landed `def-sfb-tori-multiplicative-type`, whose
recorded `MultiplicativeType.splitTorus` supplies the actual product of multiplicative groups.

The inherited BLOCKED ending concerned a stage-1 unchanged-split gate. This node is listed
in `coord/queue.tsv` at stage 2 and has no Lean record or released repair note. The stage handoff
in `coord/brief-stage2.md` section 0 explicitly permits stating such a reviewed split.
The current example `CompactObject.lean` is withdrawn and contains no declarations; this module
uses the required `module`, `public import`, and `@[expose] public section` conventions.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering and meaning |
| --- | --- |
| Algebraically closed field F | `(F : Type u) [Field F] [IsAlgClosed F]`. These are the recorded standard field and algebraic-closure notions. |
| Integer r at least zero | `(r : ℕ)`, allowing zero. |
| T is the rank-r split torus | `T : Grp (Over (Spec (.of F)))` with `hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r)`. The isomorphism is in group schemes over F, so specifies the displayed product with its group law, rather than only an isomorphism of schemes. This is a presentation of the given split torus, invariant under renaming its model; it adds no condition beyond the displayed product. |
| Trivial group at r = 0 | `splitTorus F 0` is definitionally the tensor unit in the cartesian category of group objects. |
| An F-scheme X with an action morphism T times X to X | `X : CategoryTheory.Mod (Over (Spec (.of F))) T.X`. Its underlying F-scheme is `X.X`, its underlying scheme is `X.X.left`, and the action is `ModObj.smul`. The tensor product in `Over (Spec (.of F))` is the fibre product over F. All action maps are over F. |
| Identity and associativity as morphism identities | The two fields `ModObj.one_smul` and `ModObj.mul_smul` of the bundled action. These are identities in the scheme category, including on all nonreduced test schemes, rather than an action only on F-points. |
| Separated over F | `[IsSeparated X.X.hom]`, the diagonal closed-immersion condition from `def-weil-proper-morphism`. Properness is not assumed. |
| Finite type over F | `[LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]`, precisely the recorded conjunction defining finite type. |
| Every local ring is an integrally closed domain | `hnormal : ∀ p : X.X.left, IsDomain (X.X.left.presheaf.stalk p) ∧ IsIntegrallyClosed (X.X.left.presheaf.stalk p)`. The stalks are the actual local rings, and `IsIntegrallyClosed` uses their fraction rings. This is the dependency's explicit normal-domain encoding; no global domain assumption is imposed. |
| Every point x of the underlying space | `(x : X.X.left)`. This is an arbitrary topological point of a scheme, with no closed-point or rational-point assumption. |
| An affine open subscheme U of X | The existential `U : CategoryTheory.Mod (Over (Spec (.of F))) T.X` and `i : U ⟶ X`, with `IsOpenImmersion i.hom.left ∧ IsAffine U.X.left`. An open immersion identifies U with its image as an open subscheme, carrying the restricted structure sheaf; affineness is the ordinary scheme notion. |
| U contains x | `x ∈ Set.range i.hom.left`. The underlying map is the same open inclusion up to the canonical identification with its image. |
| Restricted action factors through U and satisfies the action laws | The existential U carries its own `ModObj` structure; `i : U ⟶ X` is a morphism of these actions. Its equivariance identity is `ModObj.smul ≫ i.hom = (T.X ◁ i.hom) ≫ ModObj.smul`. Thus, after forgetting to schemes, the original action on T times U factors through U. The identity and associativity laws are part of U's bundled action. Conversely, the factorization in the node supplies precisely this bundled object and equivariant arrow by canceling the open inclusion. |
| Inclusion equivariant | Built into `CategoryTheory.Mod.Hom.isModHom`, hence into the quantified morphism `i`, rather than left as an unspecified map. |
| No further hypotheses | There are no smoothness, projectivity, irreducibility/integrality, faithfulness, or characteristic binders. All points and all algebraically closed fields in universe u are covered. |

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  reexported through the recorded algebraic-closure module.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; read the upstream group-scheme convention in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` as well.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and
  `multiplicativeGroup`, `Sheaf.AlgebraicGeometry.StandardGroupSchemes`. The former is the
  real Laurent spectrum and the latter its canonical Hopf group structure; these are the
  factors used by the existing split-torus definition.
- Added landed definition node `def-sfb-tori-multiplicative-type`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`, `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`.
  Read its full recursive construction: zero is the unit, successor is the product of G_m
  with the preceding torus. No private copy is defined here.
- `def-pc-scheme` and `def-weil-affine-spectrum`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is `IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-proper-morphism`: the recorded `IsSeparated` component, imported through
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; its signature and diagonal definition were
  read in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`, from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compact import.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`, with the latter from the
  recorded `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. The node's localization
  condition for a general ring is not substituted for the local rings already named here.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; these are the cartesian
  products in the category of schemes over F used in `ModObj`.
- `def-weil-open-immersion`: `IsOpenImmersion`, `Mathlib.AlgebraicGeometry.OpenImmersion`.
- Existing Mathlib action interfaces, without a new notion: `CategoryTheory.ModObj`,
  `CategoryTheory.Mod`, `CategoryTheory.Mod.Hom`, `CategoryTheory.IsModHom`,
  `Mathlib.CategoryTheory.Monoidal.Mod`, via `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`.
  Read both the action-law fields and the equivariance field in their definitions.

Stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal`,
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`,
`WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`, and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. The open-immersion proof dependency
is already a public statement import. Read the homogeneous-ideal module's full signature,
chart fractions, quotient grading, quotient map, and proof docstring; read the Proj chart
and covering signatures and the upstream `Proj.isAffineOpen_basicOpen_and_nonempty_iso`.
The other five proof prerequisites currently have no recorded Lean declaration or Mathlib
match, so have no module to import: `lem-trf-split-lattice-torus-projection`,
`lem-sfb-sumihiro-invariant-quasiprojective-open`,
`lem-sfb-normal-quasiprojective-equivariant-immersion`,
`lem-sfb-projective-invariant-boundary-ideals`, and
`lem-sfb-split-torus-representation-weight-decomposition`. None is a missing notion in the
statement being written. The theorem docstring preserves all six accepted proof steps and
their named inputs, including the positive-degree correction, decomposition inside the
boundary ideal itself, and the scheme-level action on nonreduced test algebras.

Edge cases checked before writing:

- Empty X: the theorem quantifies over `x : X.X.left`, so there is no obligation.
- Rank zero: permitted by `r : ℕ` and the existing zero clause of `splitTorus`; this reduces
  mathematically to existence of ordinary affine neighbourhoods for the trivial action.
- Disconnected normal X: normality is imposed stalk by stalk, not by `IsIntegral X` or a
  domain condition on all global sections. Disjoint normal components are included.
- Ineffective and trivial actions: `Mod` requires precisely the two laws and imposes no
  injectivity condition on the action or a representation.
- Nonclosed points: the point binder is the full underlying scheme type; no residue field
  is identified with F. An open immersion and range membership give a genuine neighbourhood.
- Every characteristic, including positive characteristic: no characteristic binder appears.
- Invariance is not weakened to F-points: it is the `IsModHom` identity of scheme morphisms,
  so is valid after every test-algebra extension, including nilpotent test algebras.
- No implicit universes or variables: `u` and every binder are explicit, with both
  `autoImplicit` and `relaxedAutoImplicit` disabled.

Searches actually run through `msearch.py` for this item:

- LeanFinder: `Every point of a normal finite type scheme with split torus action has an invariant affine open neighbourhood`.
  Eight hits: ordinary affine covers, affine-neighbourhood basis and reduction to affine
  neighbourhoods; none supplies a torus invariance conclusion.
- Loogle: `"Sumihiro"`. Successful search, zero hits.
- Mathlib grep: `Sumihiro|sumihiro|[Ii]nvariant.*[Aa]ffine`, subdirectory `AlgebraicGeometry`.
  Successful search, zero hits.
- LeanSearch: `Normal finite type schemes over an algebraically closed field with torus action have invariant affine open neighbourhoods`.
  Eight hits, including `exists_isAffineOpen_mem_and_subset`, `affineOpens`, and
  `Scheme.exists_affine_mem_range_and_range_subset`; these are ordinary neighbourhoods
  with no action or invariance condition.
- Direct `rg` in project `lean/Sheaf` and upstream `lean/WeilConjectures`, for `Sumihiro`,
  `sumihiro`, `torus`, `Torus`, invariant affine opens, `splitTorus`, and action interfaces.
  Found the existing `ToriMultiplicativeType` construction and `TorusInvariantAffineFiltration`.
  The latter uses this item as a prerequisite; its weaker filtration theorem is not this
  statement. Read its action encoding and used the same existing Mathlib notion.
- Direct node-id search in upstream `lean/WeilConjectures`: no declaration for this node.
  Direct full-declaration-name search in Mathlib, upstream Lean, project Lean and
  `dag/lean_names_upstream.json`: no conflicting declaration.

Sources: read the node and its entire accepted proof and review; read Milne's available PDF,
printed pp.271--273 (especially Definition 13.45 and Lemma 13.46) and p.480. Milne's projective
eigenvector charts support the chart argument but do not state this full normal-scheme theorem.
Sumihiro's paper remains marked WANTED in the node, which is retained explicitly in the Lean
docstring. This statement-only delivery does not claim to have read an absent paper or proved
the Sumihiro prerequisite. No mathematical statement fault or STATEMENT-DISPUTED flag is raised.

Validation: `scompile.py Q01 lem-sfb-sumihiro-normal-torus-affine-neighbourhood` compiled the
delivered module both as a sandbox module and at its real library module name, with no errors
or warnings (7.5 seconds and 4.3 seconds respectively). The prescribed `deliver2.py --no-push`
then returned `OK`: the delivery passes the server preflight and compiles. The node signature
is verbatim from the file; its only changed keys are `lean` and the added existing `stmt_deps`
entry. The longest source line is 92 characters. Delivery uses the same wrapper and checks.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
