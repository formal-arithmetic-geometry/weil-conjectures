## Worker report

The delivery states `AlgebraicGeometry.exists_semilinear_sylow_snc_resolution` in
`Sheaf.AlgebraicGeometry.SemilinearSylowSNCResolution`. Its only theorem has proof
`sorry`. It introduces no definitions, axioms, extra nodes, dependency repairs or
statement correction. The node is unchanged except for its `lean` record.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X 2.3,
printed pp. 151--152 (PDF pp. 157--158): Step 2 and diagram (2.c), then Step 3
and diagrams (2.d), (2.e). In particular the final paragraph on p. 152 obtains
smoothness over S', and takes the reduced inverse image of Z as a subdivisor
of the resolved relative SNC divisor. This is the support used here; it need
not be the entire auxiliary divisor introduced during modification.
The current blueprint's direct-image stability route was searched under
`literature/blueprint/latest/`; this added node has no imported blueprint ancestor,
as its existing blueprint record says.

Hypothesis correspondence (all objects are bound explicitly, `autoImplicit false`):

- The fields e and K and finite extension K/e are `e K : Type u`, `[Field e]`,
  `[Field K]`, `[Algebra e K]`, `[Module.Finite e K]`.
- The prime different from the characteristic is `ell`, `hell : ell.Prime`,
  `hchar : ell ≠ ringChar e`; characteristic zero is included.
- B and Y are `Scheme.{u}`, with structure maps `b` and `p`. B is nonempty by
  `[Nonempty B]` and proper by `[IsProper b]`. Properness includes local finite
  type and universal closedness, hence quasi-compactness and finite type.
- B is normal exactly by `hBnormal`: each stalk is a domain and integrally closed.
  Its finite disjoint integral decomposition is `hBcomponents`: finitely many
  integral open subschemes, pairwise disjoint, with supremum top. Each open is
  also closed since its complement is the union of the other opens. Thus this
  is precisely a finite disjoint union, without assuming B integral or connected.
- The finite group is `G : Type v`, `[Group G]`, `[Finite G]`. Its action on K
  by e-automorphisms is `ρ : G →* (K ≃ₐ[e] K)`.
- `hfixed` says `IsPurelyInseparable e (IntermediateField.fixedField ρ.range)`.
  Finiteness of this intermediate field follows from K/e; no faithfulness is imposed.
- Y is smooth and projective over K by `[Smooth p]`, `[IsHProjective p]`.
  This is the finite-dimensional projective-space convention of def-kun-projective.
- `a : G →* Aut Y` is the scheme action. `hequivariant` uses `ρ g⁻¹` on
  constants, because Spec is contravariant. Together with the e-linearity of ρ
  this makes each scheme automorphism an e-automorphism.
- `h`, `hbase`, `hinvariant`, `hhprojective`, `hhsurjective` express respectively
  the morphism to B, its e-linearity, its invariance, projectivity in the
  projective-bundle convention, and surjectivity.
- `hhgeneric` quantifies over every component generic point using `genericPoints Y`:
  its image is in `genericPoints B` and the canonical `residueFieldMap` is finite.
- `Q` and `q` supply the subgroup quotients. `hfinite` and `hqsurjective` are their
  finite surjective scheme maps, and `hqinv` is invariance. `hcat` is the exact
  categorical universal property for every invariant map to any scheme of the
  ambient universe. `hgeom` gives surjectivity and orbit fibres on geometric points.
- `hsections` identifies the image of each injective structure-sheaf section map
  with the invariant sections. Pullback and restriction are compared by `appLE`
  on common subopens, avoiding transports between equal opens. Finite surjective
  scheme maps are closed quotient maps, so the geometric quotient topology is
  already present. The formula uses existing section maps, not a new quotient
  definition or a replacement of the group action.
- `d` and `hd` supply the unique descents of the invariant h through the quotients;
  their existence follows from `hcat`, and uniqueness makes them the induced maps.
  Supplying these maps is equivalent to naming the descents in the informal statement.
- `hdense` is one dense open V of B meeting every generic point on which the
  descended full quotient (`d ⊤`) is finite and a universal homeomorphism. The
  latter is exactly `(topologically IsHomeomorph).universally` on the restriction.
- `C`, `hC` give the closed subset. The actual reduced inverse image D is bound
  by `hD`, the radical of the comap of its vanishing ideal, rather than merely
  an unspecified divisor with that support. `hDsnc` uses the recorded relative
  smooth strict normal crossings divisor predicate for D and p.

Conclusion correspondence:

- `∃ L : Subgroup G`, its ell-power cardinality, and `Nat.Coprime L.index ell`
  express exactly the specified Sylow subgroup (for finite G these characterize it).
- `F : IntermediateField e K` and its equality to
  `IntermediateField.fixedField (L.map ρ)` identify the actual fixed field.
  `Module.Finite e F` and `Nat.Coprime (Module.finrank e F) ell` give its finite
  prime-to-ell degree; `Module.Finite F K` and `Algebra.IsSeparable F K` give
  the stated finite separable extension, without strengthening it to Galois.
- `sF` with `q L ≫ sF = p ≫ Spec.map (CommRingCat.ofHom F.subtype)` is the
  canonical descended F-structure on Q L. This is characterized by categorical
  uniqueness, not an unrelated chosen F-structure.
- `U : (Q L).Opens` and `IsClosed (U : Set (Q L))` give Q-circle clopen. The
  family A of irreducible components with union U gives exactly a union of
  components. `q L ⁻¹ᵁ U` is Y-circle and its `IsClosed` clause makes it clopen.
- The restricted quotient is the actual `(q L).resLE U (q L ⁻¹ᵁ U) le_rfl`.
  Finite, geometric and categorical quotient properties restrict to this clopen
  subset; no new or arbitrary quotient morphism is substituted.
- The induced map d is `U.ι ≫ d L`; its projectivity and surjectivity are stated.
  The displayed composition equality is exactly h restricted = d after q.
- Every generic point of U maps to one of B, with a finite residue field map and
  `Nat.Coprime ((U.ι ≫ d L).residueDegree z) ell`. `residueDegree` is definitionally
  `Module.finrank` for the algebra induced by this precise residue field map.
- `R`, `rF`, `vR` give the resolving scheme, its F-structure and its map to U.
  `Smooth rF`, `IsHProjective rF`, `IsProjectiveBundle vR`, `Surjective vR`,
  and `vR ≫ (U.ι ≫ sF) = rF` give every smooth/projective/surjective/F-linear clause.
- `Set.BijOn vR (genericPoints R) (genericPoints U.toScheme)` is the claimed
  component-generic-point bijection. `Function.Bijective (vR.residueFieldMap η).hom`
  identifies the fields by the canonical residue inclusion, stronger in specificity
  than an unrelated abstract field isomorphism but exactly what equality means here.
- `E.IsSmoothStrictNormalCrossingsDivisor rF` includes effective Cartier,
  reducedness, distinct integral components and smooth intersections of pure
  codimension equal to the number of components, including the empty intersection.
- The first support equality is inverse image under vR of the image under the
  restricted quotient of the restriction of `D.support`. The second is precisely
  inverse image of C under d after vR. Both equalities are written, separately.
- `IsRegularScheme R` and `IsStrictNormalCrossingsBoundary E` are the two recorded
  scheme and boundary predicates, without substituting relative smoothness for them.
- At every point x, W is an affine neighbourhood, hN its stalk Noetherianity,
  t a regular parameter list, and s a sublist with `s.Nodup`. The mapped stalk ideal
  of E equals `Ideal.span {s.prod}`. A regular parameter list in a regular local
  ring is minimal, so its members give distinct nonassociate prime equations;
  radicality and the finite integral-component decomposition identify these factors
  with exactly the components through x. This is the usual local parameter criterion,
  using the same stalk-ideal representation as the existing
  `isStrictNormalCrossingsBoundary_iff_parameters` declaration.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.Algebra.Algebra.Defs: `Algebra`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsProper`;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`, together
  with quasi-compactness supplied by properness.
- Mathlib.AlgebraicGeometry.Properties: `IsIntegral`.
- Mathlib.FieldTheory.PurelyInseparable.Basic: `IsPurelyInseparable`;
  Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`.
- Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: `IsProjectiveBundle`.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: `Surjective`.
- Mathlib.Topology.Irreducible: `irreducibleComponents`; Mathlib.Topology.Sober:
  `IsGenericPoint`, `genericPoints` (the latter packages the former for components).
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.Hom.residueDegree`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `IsFinite`;
  Mathlib.CategoryTheory.MorphismProperty.Limits: `MorphismProperty.universally`;
  Mathlib.AlgebraicGeometry.Morphisms.Constructors: `topologically`;
  Mathlib.Topology.Homeomorph.Defs: `IsHomeomorph`.
- Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor:
  `Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`.
- Sheaf.AlgebraicGeometry.IsRegularScheme: `IsRegularScheme`;
  Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary: `IsStrictNormalCrossingsBoundary`.
- WeilConjectures.RingTheory.IsRegularSystemOfParameters:
  `IsLocalRing.IsRegularSystemOfParameters`.
- Sheaf.FieldTheory.FieldTower: `FieldExtension.degree`; finite degrees here are
  represented by Module.finrank together with explicit finiteness, exactly its finite case.

Proof imports include the stated good-component selection and clopen quotient lemma,
Mathlib's Sylow/smooth-restriction/closed-immersion declarations, and the projectivity
and SNC definitions. The semilinear-projective-geometry and tame-resolution proof nodes
have no Lean binding in the current DAG, so they have no module to import yet. This does
not prevent stating the present theorem: every notion in its signature already exists.
One issue inherited in the proof plan is the maintainer's existing review note that
lem-sfb-tame-snc-quotient-resolution does not explicitly assert F-linearity of its map v.
The present node explicitly does, and that clause is stated here; no sibling node is edited.
The cited ILO construction is over S', so the F-linearity is supported by the source.

Edge cases checked before writing and on final reading:

- Empty C: D and E have empty support, the SNC component families may be empty,
  and the local parameter sublist s may be empty with product 1 (the unit ideal).
- C = B is not silently excluded: for nonempty Y it cannot satisfy the Cartier
  hypothesis on D, so the implication has precisely the original hypotheses.
- Trivial G and trivial L are allowed (order ell^0); actions on either Y or K
  may have kernels. No faithfulness, geometric integrality or perfectness is assumed.
- B, Y, U and R may be disconnected. Prime-to-ell degrees are imposed separately
  at each generic point of U, not just on a sum of component degrees.
- Dimension zero permits empty regular parameter lists. Off the boundary, the
  empty sublist gives the unit ideal. Empty component intersections are allowed.
- An empty U would contradict its surjection to the nonempty B, not an additional
  nonemptiness hypothesis. Likewise Y cannot be empty because h is surjective.
- The finite group universe v is independent of the scheme/field universe u.
  Geometric tests range over fields of the scheme universe; algebraic closures
  of residue fields are available there, as in the published quotient interfaces.

Searches actually run with the prescribed msearch wrapper:

1. leanfinder: "A finite semilinear group action on a smooth projective scheme with
   strict normal crossings boundary admits a Sylow quotient and smooth projective
   resolution preserving generic residue degrees". Eight hits: Frobenius/invariant
   prime results, polynomial factorization and smooth-algebra results; no match.
2. loogle: `Sylow, AlgebraicGeometry.Scheme`. Zero hits.
3. grep: `normalCrossing|normal_crossing|semilinear.*quotient|Sylow`, restricted to
   Mathlib/AlgebraicGeometry. Zero hits.
4. leansearch: "Semilinear Sylow quotient resolution of a smooth projective scheme
   with a normal crossings boundary". Eight hits on smoothness and Sylow group
   theory; no matching combined geometric theorem.
5. Local rg in lean/WeilConjectures and lean/Sheaf for the item id and
   `semilinear.*sylow|semilinear_sylow|SemilinearSylow` found the existing
   good-component selection interface and the global alteration's proof description,
   not a statement of this resolution lemma. Read the full former signature and
   docstring. The upstream-name map also has no matching resolution declaration.
6. Read the existing SNC divisor, boundary, regular scheme, parameter-system,
   projective morphism, admissible quotient, field-degree and parameter-criterion
   definitions. No duplicate notion was needed or introduced.

Validation: the module passed scompile.py against the live server library with no
errors or warnings; the statement contains exactly one `sorry` proof.

## Second reading by Q72

Performed a fresh clause-by-clause reading in this same worker session, following
this dispatcher's prohibition on starting other agents; this is not a claim of an
independent agent review. The maintainer's independent delivery review remains required.

Reopened the node statement, the emitted theorem and the source pp. 151--152. Checked
that finite type for B follows from its properness rather than being dropped;
that generic-point degrees use the canonical field map and explicit finiteness;
that no faithful-action or perfect-field assumption entered; that K/F is stated
finite separable rather than strengthening the conclusion to Galois; and that vR
is explicitly a morphism over the descended F-structure. Both inverse-image support
equalities are present. The actual restricted quotient is used throughout.

The first draft reused the stronger admissible-quotient packaging from the
existing good-component lemma; before compiling it was replaced with the node's
finite/categorical/geometric/invariant-section clauses explicitly. In particular
there is no additional chosen affine orbit neighbourhood hypothesis. The parameter
clause uses a product of a nodup sublist of a regular parameter list, and permits
the empty product. Finally added direct public imports for the existing field-tower
and regular-scheme nodes. No statement correction, new node or unresolved statement
dispute was found. The source-supported F-linearity issue in the unstated proof
sibling is reported above rather than silently weakening this item's conclusion.
