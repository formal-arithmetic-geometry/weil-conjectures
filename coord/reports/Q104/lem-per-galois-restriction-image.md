## Worker report

The module `Sheaf.FieldTheory.SeparableClosureRestrictionImage` states
`IntermediateField.separableClosure_restriction_image`, with its proof `sorry`.
No new definition, dependency module, or statement correction is required.
The node copy changes only `lean`.

Source read: `literature/stacks-project/fields.tex`,
`lemma-galois-profinite` (0BMJ), lines 2859 onward, and
`theorem-inifinite-galois-theory` (0BML), lines 3054–3146.
The latter identifies closed subgroups by their fixed fields, including the
full-group fixed field, and the former supplies the profinite Krull topology.
The declaration docstring carries all six steps of the node's proof and names
every proof-dependency node.

Hypotheses and clauses, matched to the node:

- Fields K and L: `(K : Type u) (L : Type v) [Field K] [Field L]`.
  The inclusion K into L is `[Algebra K L]`; field ring homomorphisms are injective.
- The chosen closures are `(Ks : Type w) (Ls : Type z)`, their field instances,
  `[Algebra K Ks] [Algebra L Ls]`, and
  `[IsSepClosure K Ks] [IsSepClosure L Ls]`.
  `IsSepClosure` means a separably closed top field and a separable algebraic
  extension, exactly as the dependency node specifies.
- The compatible embedding Ks into Ls is `[Algebra Ks Ls]` together with
  `[Algebra K Ls] [IsScalarTower K L Ls] [IsScalarTower K Ks Ls]`.
  These two towers identify the composites from K to Ls. They are structural
  compatibility data already required by the node, not extra field hypotheses.
- The two absolute Galois groups are `Ls ≃ₐ[L] Ls` and `Ks ≃ₐ[K] Ks`.
  Importing `Mathlib.FieldTheory.KrullTopology` supplies precisely the topology
  whose identity basis consists of the fixing subgroups of finite intermediate
  extensions (`galGroupBasis`, `krullTopology`, and
  `krullTopology_mem_nhds_one_iff`, read in that file).
- Well-defined restriction as a homomorphism uses the existing Mathlib
  `IntermediateField.restrictRestrictAlgEquivMapHom K Ks L Ls :
  (Ls ≃ₐ[L] Ls) →* (Ks ≃ₐ[K] Ks)`.
  Its definition restricts scalars from L to K, then restricts to the normal
  subfield Ks. The `Normal K Ks` instance follows from `IsSepClosure.isGalois`.
  Read its full definition/docstring in `Mathlib/FieldTheory/Galois/Basic.lean`
  lines 600–612 and the underlying `AlgEquiv.restrictNormalHom` and
  `AlgEquiv.restrictNormal_commutes` in `Normal/Defs.lean` lines 169–199.
  In particular it acts as restriction for the specified embedding; no
  arbitrary homomorphism, chosen lift, or existence hypothesis replaces it.
- Continuity is the first conjunct `Continuous (restrictRestrictAlgEquivMapHom
  K Ks L Ls)`.
- Closed image is the second conjunct `IsClosed ((... ).range :
  Set (Ks ≃ₐ[K] Ks))`. A homomorphism's range subgroup has exactly its image
  as underlying set.
- The final equality says that this range is
  `{σ | ∀ x : Ks, algebraMap Ks Ls x ∈ Set.range (algebraMap L Ls) → σ x = x}`.
  The membership condition selects exactly the elements of Ks whose images
  lie in L, so the universal quantifier says precisely that σ fixes every
  element of E = Ks ∩ L. Injectivity of the embedding identifies equality
  inside Ks with equality inside Ls.
- There is no algebraicity, separability, finiteness, normality, or perfectness
  hypothesis on L/K. Four independent universes cover all field sizes.

Statement-dependency declarations used, read with their docstrings and full signatures:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`,
  lines 91–101. This supplies the field embeddings throughout.
- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`,
  `IsSepClosed` (lines 61–67), `IsSepClosure` (225–229),
  `isSepClosure_iff` (258–260), and `IsSepClosure.isGalois` (267–271).

All recorded Mathlib modules for the eight proof dependencies are imported as
plain proof imports: `Mathlib.FieldTheory.IsSepClosed` (already a public
statement import), `Mathlib.FieldTheory.Galois.Profinite`,
`Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`,
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`,
`Mathlib.Topology.Separation.Hausdorff`,
`Mathlib.FieldTheory.Galois.Infinite`, and
`Mathlib.Topology.Algebra.ClopenNhdofOne`.
In particular the full arbitrary-field restriction theorem is not the finite
surjectivity theorem in Galois/Basic.lean:630–644.

Edge cases checked mathematically before writing:

- K = L with identical closures: restriction is identity, E = K, and its
  fixing subgroup is the full group.
- L contains the chosen Ks: every source automorphism fixes Ks, E = Ks,
  and the range and right side are both the trivial subgroup.
- L/K purely inseparable: E = K, so the asserted range is the whole group;
  the statement does not assume the characteristic is zero or K perfect.
- L = K(t), with the usual compatible closure embedding: E = K and the
  formula gives surjectivity. No algebraicity binder excludes this case.
- Finite separable nonnormal L/K: E is the embedded copy of L; the image is
  its fixing subgroup, which need not be normal. No normal-image clause is added.
- K separably closed: the target group is trivial and both sides are trivial.
  Field instances exclude zero rings precisely as the source's fields do.

Searches actually run, through the prescribed msearch wrapper:

- LeanFinder query: "For any field extension the image of restriction from
  the absolute Galois group is closed and equals the automorphisms fixing the
  intersection of the smaller separable closure with the larger base field".
  Eight results, including `InfiniteGalois.fixingSubgroup_isClosed`,
  `IntermediateField.fixingSubgroup_isClosed`, `fixedByFinite`, and
  `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`; no exact theorem.
- Loogle query: `"restrictRestrictAlgEquivMapHom"`. Four results: the
  canonical homomorphism and its apply, injectivity, and finite-dimensional
  surjectivity lemmas. Reused the homomorphism; the finite surjectivity lemma
  has extra finite-dimensional hypotheses and does not state the item.
- Mathlib grep query: `range.*restrict|restrict.*range|mapOfAlgebra`,
  subdirectory `FieldTheory`. Sixteen results, including the finite-dimensional
  proof in Galois/Basic.lean, but no arbitrary restriction-image theorem.
- LeanSearch query: "The restriction map from the absolute Galois group of L
  to that of K for arbitrary K inside L has image the automorphisms fixing
  the intersection of L with a separable closure of K". Eight results:
  `IntermediateField.restrictRestrictAlgEquivMapHom_surjective`,
  `AlgEquiv.restrictNormal`, `IntermediateField.restrictNormalHom_ker`,
  `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`, etc.; no exact theorem.
- Project rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  `Galois.*[Rr]estrict|galois.*[Rr]estrict`, then
  `restrictRestrictAlgEquivMapHom|restriction_image|restrictionImage`.
  Results concern other geometric restriction maps and unrelated private
  definitions. Read `Sheaf/Paper/RealBoundaryLocalConstants.lean`; it states
  residue and inertia surjectivity, not this theorem.
- `grep -rn 'lem-per-galois-restriction-image' lean/WeilConjectures`:
  no matches. The new full declaration name was also searched across
  Mathlib, both project Lean roots, and `dag/lean_names_upstream.json`:
  no matches.

Validation: prescribed `scompile.py Q104 lem-per-galois-restriction-image`
passed for the delivered module, both sandbox (6.9 s) and library (7.9 s)
checks, with no unexpected warnings or errors. All universes and variables
are explicitly bound and `autoImplicit` is false.

## Second reading by Q104

A separate pass in this worker reopened the node statement and the final Lean
signature; no second agent was started, as required by the dispatcher brief.
The maintainer's independent review remains external to this delivery.

The four field binders and algebra structures match the node's fields and two
chosen closures. The two scalar towers, read against the restriction map's
Mathlib definition, express exactly compatibility over K. Both `IsSepClosure`
instances are present and neither is replaced by the stronger algebraically
closed-field assumption. The inferred Krull topology is the one in the node:
finite intermediate-field fixing subgroups, not a discrete topology.
The first conjunct is continuity of the existing canonical restriction map,
its source being Gal(Ls/L) and target Gal(Ks/K), in that order. The second
conjunct is closedness of that same map's range. The third conjunct is equality
of that same range with the pointwise fixer of exactly Ks intersect L:
`Set.range (algebraMap L Ls)` denotes L inside Ls, and the preimage under
`algebraMap Ks Ls` denotes E inside Ks. The implication binds every x in that
preimage; it neither asks that the intersection be just K nor assumes it
finite. There is no normality conclusion on the image and no algebraicity or
separability restriction on L/K. The theorem has only `sorry` as proof, and
the docstring follows each of the six recorded proof steps. No mismatch or
node fault was found, and no statement change was made.
