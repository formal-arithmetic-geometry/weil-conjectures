## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearQuotientProjectiveGeometry` states
`AlgebraicGeometry.semilinear_quotient_projective_geometry`. Its only theorem has
proof `sorry`; it contains no new definitions. The node is unchanged except for
its `lean` record. There are no statement disputes, new nodes, or dependency repairs.

Hypothesis and object correspondence:

- The fields are `(e K : Type u) [Field e] [Field K]`; the extension is
  `[Algebra e K]`, and finiteness is `[Module.Finite e K]`, without separability.
- The finite group is `(H : Type v) [Group H] [Finite H]`. Its action by
  e-automorphisms is `ρ : H →* (K ≃ₐ[e] K)`.
- F is exactly `IntermediateField.fixedField ρ.range`, used explicitly throughout.
  Taking the image does not assert faithfulness: fixedness under the image and
  fixedness under every element of H are identical conditions.
- The schemes are `(Y Q : Scheme.{u})`, and the specified K-structure is
  `a : Y ⟶ Spec (CommRingCat.of K)`, with `[Smooth a] [IsHProjective a]`.
- The scheme action is `α : H →* Aut Y`. The given e-structure is the composite
  `a ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))`; `hαe` says the action
  preserves this structure. `hαK` is equivariance over the scalar action.
  It uses `(ρ h⁻¹).toRingHom`: because Spec is contravariant, inversion turns
  the field action into a left scheme action, consistently with multiplication
  in `CategoryTheory.Aut`. No commutativity of H is assumed.
- The supplied quotient arrow is `(q : Y ⟶ Q) [IsFinite q] [Surjective q]`.
  Its H-invariance is exactly `hinv`.
- For each algebraically closed field Ω, `honto` states surjectivity on Ω-valued
  scheme points, and `horbits` states that equality of their images is equivalent
  to being in one H-orbit. Points are all scheme maps from Spec Ω, rather than
  only K-points or F-points, as required for the semilinear action.
- `hsections` states equality of the structure sheaf with the invariants on every
  open U of Q: `q.app U` is injective, and its image consists exactly of sections
  fixed under every pullback `(α h).hom.appLE`. The inclusion `hU` identifies
  restriction to the same inverse-image open. It always exists, since `hinv`
  makes `q ⁻¹ᵁ U` invariant; quantification over its proofs does not weaken
  fixedness. The assertion holds also on the empty open. This is the interface
  already used by the proof dependency `finiteQuotient_normal_proper`.
- `hcategorical` quantifies over every scheme T and every invariant scheme map
  f, and asserts a unique factor g with `q ≫ g = f`. T is not required to carry
  any field structure. This is categorical descent in schemes, as in the node.

Conclusion correspondence, in the order written in Lean:

- The witness `sF : Q ⟶ Spec (CommRingCat.of (IntermediateField.fixedField ρ.range))`
  is a structure map for this actual fixed field. The first equation states
  `q ≫ sF = a ≫ Spec.map (algebraMap F K)`. The next quantified clause states
  uniqueness among ALL structure maps satisfying that equation, independently
  of the remaining geometric conclusions.
- The next equation makes q an e-morphism for the e-structure induced by sF;
  the quantified `se` clause says that any e-structure descending the given
  e-structure equals that induced structure. Together with the first equation,
  these give exactly the stated F- and e-compatibilities and descended e-structure.
- Normality of Y is `∀ y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y)`. Noetherianity is `IsNoetherian Y`.
- The finite clopen decomposition uses `n : ℕ` and `U : Fin n → Y.Opens`:
  their underlying sets enumerate `irreducibleComponents Y`, are closed and
  pairwise disjoint, and their supremum is top. Each open subscheme is integral
  with normal stalks. `Nonempty (IsColimit (Cofan.mk Y ...))` expresses the
  actual scheme coproduct with these canonical open inclusions. Integral
  clopen summands are precisely the irreducible components, so this does not
  strengthen the claimed finite disjoint decomposition.
- `IsHProjective` of the two actual structure-map composites gives projectivity
  of Y over F and over e, in the dependency's finite-projective-space convention.
- Normality of Q is the same stalk condition; `IsNoetherian Q` gives its
  Noetherianity. `IsHProjective sF` is projectivity over F in the required convention.
- `IsProper sF` and `LocallyOfFiniteType sF ∧ QuasiCompact sF` state properness
  and finite type over F. The last two clauses state these properties for the
  induced e-structure `sF ≫ Spec.map (algebraMap e F)`.
- There is no assertion that a quotient exists: Q and q are given parameters.

Dependency declarations used for the statement (all signatures and docstrings read):

- `def-weil-field`: Mathlib `Field`, from `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: Mathlib `Algebra` and `algebraMap`, from
  `Mathlib.Algebra.Algebra.Defs`. The field structure morphism is `Spec.map`.
- `def-sfb-finite-infinite-set`: `Set.Finite`, from `Mathlib.Data.Finite.Defs`,
  is finiteness of the subtype; `[Finite H]` is the corresponding whole-type form.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`, from the canonical
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, not the retired duplicate.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`, from
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, from
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-irreducible-components`: `irreducibleComponents`, from
  `Mathlib.Topology.Irreducible`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, from the recorded finite-type/quasi-compact APIs.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`, with the latter
  from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`; applied to local rings.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, from
  `Mathlib.RingTheory.Noetherian.Defs`. The standard scheme predicate
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian` is
  equivalent to a finite affine cover with Noetherian section rings, by
  `isNoetherian_iff_of_finite_iSup_eq_top`. Thus it is precisely the node's convention.
- Fixed fields use the existing `IntermediateField.fixedField` and
  `IntermediateField.mem_fixedField_iff` in `Mathlib.FieldTheory.Galois.Basic`.
  No additional fixed-field notion or quotient predicate is introduced.

All proof dependencies with a recorded module are imported, without `public`
when used only for the proof. In particular these are the recorded regularity,
normal decomposition, finite quotient normal/proper, projective ample invertible,
closed immersion, ample restriction, finite normal ample descent, invertible and
ample module, proper relative ample, and projective bundle to H-projective modules.
`lem-sfb-finite-constant-projective-graph` and
`lem-weil-pbc-finite-type-over-noetherian` have no Lean record in the read DAG;
there is no module recorded to import for those proof-only prerequisites. They
are not needed to type the statement. The theorem docstring reproduces all eight
DAG proof steps, including their dependencies and sources.

Edge cases checked before and after writing:

- Empty Y forces empty Q by the supplied surjection. The structure maps and their
  descent are unique, stalk assertions are vacuous, and the component witness
  may use `n = 0`. No integral or nonempty hypothesis is imposed on Y or Q.
- Disconnected smooth Y is handled by the finite family of normal integral opens;
  no geometric connectedness or geometric integrality is required.
- A trivial scalar action gives fixed field K; a nonfaithful action gives exactly
  the same fixed field as its image. Neither action is required to be injective.
- K/e may be inseparable, and the characteristic may divide the group order.
  No averaging, linearization, tame action, or quotient smoothness is assumed.
- The group universe v is independent. Fields and schemes use a common universe u,
  and geometric test fields use that same u, as in the existing finite-quotient
  statement. For any particular collection of fields/schemes they can be placed
  in such a common universe; no independently smaller test universe is introduced.
- The e-structure on Q is a conclusion, not an input or an arbitrary chosen map.
- The finite-projective-space convention is preserved for every projectivity clause.

Sources opened: the supplied node and all statement dependency records, the recorded
Lean declarations and docstrings; ILO printed p.151 (PDF page 157), including diagram
(2.c), and the current blueprint direct-image proof; Stacks `divisors.tex`,
`proposition-push-down-ample`, case (2). The example CompactObject module is now a
withdrawn empty module in the live read checkout; current delivered modules supplied
its module/import/public-section conventions instead.

Searches for an existing statement, using the prescribed msearch wrapper:

- LeanFinder query: “A supplied finite geometric categorical quotient of a smooth
  projective scheme by a semilinear finite group action is normal Noetherian and
  projective over the fixed field”. Eight hits, on projectivization cardinality,
  Galois categories, projective representations, Proj properness and invariant
  actions. None states this scheme result.
- Loogle query: `IntermediateField.fixedField, AlgebraicGeometry.IsHProjective`.
  Zero hits; the service does not know the project's `IsHProjective` declaration.
- Mathlib grep query: `semilinear.*quotient|quotient.*projective|def fixedField`.
  Eleven hits, including the existing fixed-field definition at Galois/Basic:210;
  none is this theorem.
- Repository ripgrep for `semilinear`, fixed fields and `finiteQuotient` in the
  geometry modules found the fixed-field API uses, the finite quotient theorem,
  and SemilinearSylowGoodComponents. The latter has additional global data and
  only concludes properties of selected components, so is not this theorem.
- Search for the exact item id in `lean/WeilConjectures` returned no declaration.
  Broader searches for `semilinear.*quotient|quotient.*semilinear` in both source
  roots found coefficient-system statements and the global-model results, not
  the assigned supplied-quotient geometry statement.

Validation: `scompile.py NX lem-sfb-semilinear-quotient-projective-geometry` compiled
this module both as a sandbox probe and under its final library module name,
with no errors or disallowed warnings (26.2 s and 18.5 s respectively). Both
implicit-variable options are disabled in the module. No local notation, local
instance, scratch declaration, or data-valued sorry is present.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
