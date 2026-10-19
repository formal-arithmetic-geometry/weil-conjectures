## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeProjInvertibleTwist` states
`AlgebraicGeometry.exists_unique_relativeProj_invertible_twist`, with `sorry` as its entire
proof. No definitions are introduced, no other theorem is stated, and no node field except
`lean` is changed. Source read: Stacks Project constructions.tex,
lemma-twisting-and-proj (Tag 02NC), including the preceding graded-twist construction and
its trivialize-and-glue proof. This is its specialization to Sym(E) and L tensor-power n.

Hypothesis and clause audit:

- The arbitrary scheme S is `(S : Scheme.{u})`, with `universe u` explicitly declared.
- The two O_S-modules are `(E L : S.Modules)`; these are sheaves of modules on S, not
  modules merely over the ring of global sections.
- Quasi-coherence and finite type of E are `[E.IsQuasicoherent] [E.IsFiniteType]`, the
  Mathlib notions used by the recorded `pqf-def-coherent` module. Coherence, finite
  presentation, local freeness, and Noetherian hypotheses are not imposed.
- Invertibility is `[L.IsInvertible]`, specifically `Scheme.Modules.IsInvertible`.
- The nonnegative integer is `(n : ℕ)`, including zero. The twist is `E ⊗ L.tensorPow n`.
  The existing `tensorPow` has the structure sheaf as its zeroth term.
- P(E) is `(SymmetricAlgebraSheaf.gradedAlgebraData E).relProj`; the target is the same
  construction for `E ⊗ L.tensorPow n`. These are exactly the canonical symmetric
  algebras, symmetric gradings, and relative Proj used by `IsProjectiveBundle`.
- The quasi-coherence proof needed to form the target is supplied by the existing theorem
  `Scheme.Modules.isQuasicoherent_tensorObj E (L.tensorPow n)`; it is not a new hypothesis
  or an existential choice of algebra or Proj realization. The existing tensor-power
  invertibility instance supplies its second input condition.
- The isomorphism over S is `∃! e : ... ≅ ..., e.hom ≫ ...relProjHom = ...relProjHom ∧ ...`.
  The over-S equation is the explicit commuting triangle; the inverse triangle follows
  from e being an isomorphism.
- The word canonical is rendered by a local normalization, and uniqueness is only among
  isomorphisms satisfying this normalization. It does NOT assert uniqueness among all
  S-isomorphisms of the two schemes. For every affine U and every free generator s of
  `L.tensorPow n` on U, the inverse of e is induced by a graded ring map β fixing the
  coefficients and sending `ι(v)` to `ι(tmulSection v s)`. These are the two quantified
  equations for β. Existence of β and its irrelevant-ideal condition is part of the
  conclusion, so the local normalization cannot hold vacuously because no map was supplied.
  The formula `...relProjι U ≫ e.inv = Proj.map β hβ ≫ ...relProjι U` specifies the local
  map in the canonical affine charts. `hβ` is the actual domain condition of Proj.map,
  never an additional assumption on S, E, L, U, or s.
- Allowing all frames of L tensor-power n is equivalent to using nth powers of frames
  of L as in the node proof: any two such frames differ by a unit, whose kth power
  cancels between numerator and denominator on every degree-zero Proj chart. The
  displayed generator and scalar equations uniquely determine β by the symmetric
  algebra universal property. Standard charts and affine frame opens cover, so they
  uniquely determine e. This is the canonical map in Tag 02NC, rather than extra
  geometric data or a stronger independent assertion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; arbitrary schemes, morphisms, and the affine-spectrum proof input.
- `WeilConjectures.AlgebraicGeometry.Coherent` (read with `scompile.py --source`): its
  module documentation identifies the exact Mathlib `SheafOfModules.IsQuasicoherent`
  and `SheafOfModules.IsFiniteType` notions used here. `RingedSpace.IsCoherent` itself
  is not required because E is only quasi-coherent of finite type.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, and the actual monoidal tensor structure.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: the recorded general
  sheaf tensor interface and its public `TensorProductOfUniverses` dependency. This is
  publicly imported as the recorded def-pur-sheaf-tensor-product dependency; for schemes
  the established monoidal tensor and `tmulSection` interfaces are used.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`; its body uses
  the exact `SymmetricAlgebraSheaf.gradedAlgebraData` construction used in this statement.
  That definition is in its public dependency
  `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`, which was read in full.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` (read with `scompile.py --source`):
  `Scheme.GradedAlgebraData.relProj`, `relProjHom`, `relProjι`, `relProjRestrictIso` and
  the affine restriction compatibilities. The local formula is expressed through
  `relProjι`, so it uses these exact canonical relative-Proj charts.
- Existing concrete normalization interfaces, also read in source:
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`, `Scheme.Modules.tmulSection`;
  `...Modules.FreeGenerator`, `Scheme.Modules.IsFreeGenerator`;
  `...Modules.ProjectionFormula`, `IsInvertible.tensorPow`, `isQuasicoherent_tensorObj`;
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`, `AlgebraicGeometry.Proj.map`.

Proof dependencies are imported without `public` when not already present through the
public statement imports: `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`
(`lem_nagata_affine_proj_scalar_extension`) and `Mathlib.AlgebraicGeometry.Gluing`
(`Scheme.Cover.glueMorphisms`, `hom_ext`). The remaining recorded proof inputs are publicly
available transitively: `Scheme.isBasis_affineOpens`,
`exists_quasiCoherentSymmetricAlgebra`, `SymmetricAlgebra.graded_by_tensor_images`,
`HomogeneousLocalization.Away`, `Spec`, `Proj.basicOpenIsoSpec`,
`Proj.iSup_basicOpen_eq_top`, and the statement dependencies listed above. Their signatures
and source documentation were read, using `scompile.py --source` for server-only modules.
The declaration docstring includes all seven steps of the node's proof, including
unit cancellation, restriction compatibility, inverse gluing, and independence of frames.

Edge cases checked mathematically before drafting: n = 0; L trivial; E = 0 (both Proj
schemes empty); S empty (unique empty-scheme map, with the frame condition harmless);
nonreduced bases, positive characteristic, and zero divisors in homogeneous denominators
(the proof cancels only units); non-quasi-separated S (overlaps need affine refinements,
not affine intersections); E finite type without local freeness or coherence. In all
cases the statement retains the same scheme and sheaf constructions. The coefficient
ring may be zero on an empty affine open. The universe u is arbitrary and all binders
and universes are explicit; `autoImplicit` is false.

Searches for an existing statement:

- `msearch.py leanfinder`, query "Relative projective bundle is canonically unchanged by
  tensoring with a power of an invertible sheaf": 8 hits, including
  `Proj.pullbackAwayιIso` and its identities, `Proj.pow_apply`, and an unrelated condensed
  projectivity result. None states invariance of a relative projective bundle by a line
  bundle twist.
- `msearch.py loogle`, query `AlgebraicGeometry.Proj, SymmetricAlgebra`: 0 hits.
- `msearch.py grep`, query
  `twisting.and.proj|relative.*[Pp]roj.*invertible|[Pp]roj.*[Tt]ensor`, directory
  AlgebraicGeometry: 0 hits.
- `msearch.py leansearch`, query "relative Proj symmetric algebra tensor invertible sheaf
  canonical isomorphism": 8 hits concerning stalks, ordinary symmetric-algebra quotient
  maps, and standard affine charts; no match.
- `rg` in WeilConjectures and lean/Sheaf for combinations of Proj, projectiveBundle,
  invertible, twist, tensor: existing twisting sheaves on Proj, projective-space results,
  and tautological geometry were found, but no theorem of this statement. The canonical
  symmetric graded algebra and tensor interfaces found there are reused.
- Search of WeilConjectures for the item id: no hit; search in dag/lean_names_upstream.json
  and source trees for the proposed declaration name: no hit.

No statement fault or disputed statement was found. No new node or dependency repair
is needed. The sole postponed proof is the named theorem for this DAG item.

Validation: prescribed `scompile.py Q137 lem-trf-relative-proj-invertible-twist <file>`
passed both sandbox and final module compilation without errors or warnings.

## Second reading by Q137

Author's self-check for direct worker delivery; independent review is performed by the
maintainer. Re-read the node and the final signature together: S, E, L, quasi-coherence,
finite type, invertibility, and n are exactly the binders described above. Both objects
are the relative Proj of the canonical symmetric algebra, and the commuting triangle is
explicit. Checked carefully that the local formula uses e.inv: the algebra map goes
Sym(E) → Sym(E tensor L^n), so its Proj map goes in the opposite direction. The coefficient
and degree-one equations force the local symmetric map, and the affine frame formula
specifies canonicity; uniqueness is conditional on that formula, not merely on being over S.
The target's quasi-coherence is derived, not assumed. No mathematical correction was
needed after compilation. Every theorem proof in the delivered module is exactly `sorry`.
