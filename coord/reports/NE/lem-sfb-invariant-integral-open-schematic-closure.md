## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantIntegralOpenSchematicClosure` states
`AlgebraicGeometry.invariant_integral_open_schematic_closure`. Its only proof is
`sorry`, with the seven-step DAG proof in the declaration docstring. There are
no definitions, auxiliary assertions, new nodes, dependency repairs, or statement
corrections. The node copy changes only `lean`.

Hypotheses, in the order of the node:

- The field is `(k : Type u) [Field k]`. Its specified spectrum is `Spec (.of k)`;
  `(X P : Scheme.{u}) [IsIntegral X]` gives the integral scheme X and the ambient
  scheme P. The specified structure morphism is `(f : X ⟶ Spec (.of k))`.
- P is Noetherian exactly through `[IsLocallyNoetherian P] [CompactSpace P]`.
  These are the two conditions named in the node, with no separation assumption.
- The specified map to X is `(r : P ⟶ X)`.
- The finite group is `(H : Type v) [Group H] [Finite H]`, independently of u.
  The left actions are monoid homomorphisms `a : H →* Aut X`,
  `A : H →* Aut P`, and `b : H →* Aut (Spec (.of k))`. Multiplication of
  categorical automorphisms is the usual left-action composition convention.
- The field action is `rho : H →* (k ≃+* k)`. The equation `hb` identifies
  `(b h).hom` with `Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)`, including
  the required inverse group element under the contravariant Spec construction.
- `hf` states `(a h).hom ≫ f = f ≫ (b h).hom`; `hr` states
  `(A h).hom ≫ r = r ≫ (a h).hom`. These are precisely the two commutative
  squares in the node, in Lean's order of composition.
- `(U : X.Opens)` and `hU : Dense (U : Set X)` specify the dense open.
  `hUinv : ∀ h, (a h).hom ⁻¹ᵁ U = U` is invariance. Because each a_h is an
  automorphism, preimage invariance is equivalent to image invariance.
- `[IsIso (r ∣_ U)]` is exactly the restriction r⁻¹(U) → U being an isomorphism.
- `(j : U.toScheme ⟶ P)` together with
  `hj : j = inv (r ∣_ U) ≫ (r ⁻¹ᵁ U).ι` names the specified inverse open
  immersion. This is a completely determined map, not an arbitrary immersion
  or an additional geometric assumption. Every instance in the node supplies
  it by this formula. There is no extra open-immersion or integrality hypothesis
  on U or on T.

Conclusions, clause by clause:

- The specified T is literally `j.image`, c is `j.imageι`, j_T is `j.toImage`,
  and q is `j.imageι ≫ r`; all are the canonical Mathlib schematic-image
  constructions. Their factorization equality is `j.toImage_imageι`.
- `j.ker = Scheme.IdealSheafData.vanishingIdeal
  (Closeds.mk (closure (Set.range j)) isClosed_closure)` identifies the defining
  ideal with the reduced induced closed structure on the stated closure.
  `Set.range j.imageι = closure (Set.range j)` asserts the support equality;
  `IsReduced j.image` asserts reducedness explicitly. The canonical image
  inclusion is already a closed immersion by Mathlib's instance, not an
  additional assumption.
- `Nonempty j.image` and `IrreducibleSpace j.image` are the two stated
  topological properties. The dependent existential `∃ (_ : IsIntegral j.image),`
  asserts integrality and makes that instance available for the subsequent
  generic points and function fields. It is in the conclusion, not a hypothesis.
- `IsOpenImmersion j.toImage ∧ DenseRange j.toImage` says the actual canonical
  factor is a dense open immersion. `IsIso ((j.imageι ≫ r) ∣_ U)` says exactly
  that q⁻¹(U) → U is an isomorphism, without replacing it by an unspecified
  common open.
- For every h and every open V of P, the `Ideal.map` equality transports
  `RingHom.ker (j.imageι.app V).hom` along `((A h).hom.app V).hom` onto
  `RingHom.ker (j.imageι.app ((A h).hom ⁻¹ᵁ V)).hom`. By the ideal-sheaf
  dependency, these are exactly I(V) and I(A_h⁻¹V). This states preservation of
  the defining sheaf of ideals on every open, not just preservation of its
  support or of its radical. The section-ring transport is an isomorphism
  because A_h is an automorphism.
- The existential `aT : H →* Aut j.image` is a left action by actual scheme
  automorphisms. Its first equality is c aT_h = A_h c. The quantified equality
  for `aT'` gives uniqueness among ALL actions satisfying this first equality,
  without imposing the later q- or f-equivariance conditions on the competitors.
- The next two universal equalities state q aT_h = a_h q and
  f q aT_h = b_h f q, respectively.
- `hη : (j.imageι ≫ r) (genericPoint j.image) = genericPoint X` is the assertion
  about the generic points; Mathlib's `genericPoint_spec` supplies their generic
  point property. Uniqueness for sober irreducible spaces ensures this also
  represents any generic points denoted η_T and η_X in the node.
- `IsIso ((j.imageι ≫ r).stalkMap (genericPoint j.image))` concerns q's actual
  stalk map. Finally the equivalence `e : X.functionField ≃+* j.image.functionField`
  has its ring homomorphism equated to this stalk map after
  `X.presheaf.stalkSpecializes (specializes_of_eq hη)` identifies its source
  stalk with the stalk at η_X. This transport is along an equality of points;
  the equivalence cannot be an unrelated abstract field isomorphism. The two
  function fields carry Mathlib's Field instances for integral schemes.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme` and `def-weil-affine-spectrum`:
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, in
  `Mathlib.AlgebraicGeometry.Properties`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, in
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`, in
  `Mathlib.Topology.Defs.Filter`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-nagata-scheme-theoretic-image`: `Scheme.Hom.image`, `imageι`, `toImage`,
  in `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, and `Scheme.Hom.ker` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-sc-generic-point`: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`,
  in `Mathlib.Topology.Sober`.
- `def-sc-function-field`: the arbitrary integral-scheme clause uses
  `AlgebraicGeometry.Scheme.functionField`, in
  `Mathlib.AlgebraicGeometry.FunctionField`, as directed by the recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField`. I read that module's
  docstring: its separate component-product definition is for the general
  curve clause, and is not the carrier used for an integral scheme.
- `def-sbc-closed-immersion-ideal-sheaf`: `Scheme.Hom.ker` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`; its defining ordinary kernels
  on all opens are written explicitly for the closed immersion, as the node
  itself specifies. This supplies no second ideal-sheaf definition.

The proof-plan imports also include `Sheaf.TraceFormula.ReducedSchemeImage`
(`AlgebraicGeometry.schemeTheoreticImage_reduced`),
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` (the canonical toImage
open-immersion instance),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`AlgebraicGeometry.IsClosedImmersion.lift`, `eq_lift`), and
`WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks`
(`Scheme.exists_ringEquiv_rationalFunctionRing_pi_stalk`). The Noetherian-open
and sobriety proof dependencies are supplied by their recorded Mathlib matches:
`IsNoetherian.noetherianSpace`, the open-subscheme locally-Noetherian instance,
`NoetherianSpace.isCompact`, and the scheme's `QuasiSober` and `T0Space`
instances. These interfaces were read before writing; none needs repair.

Edge cases checked before writing:

- X cannot be empty because `IsIntegral X` includes nonemptiness. The empty U
  is excluded exactly by density in this nonempty X, without a new hypothesis.
- U = X, r an isomorphism, and X = Spec k give the expected image and identity
  generic stalk identification. The group may be trivial, and no action is
  required to be faithful.
- P may have extra components, including nonreduced components. The image
  construction discards components missed by the common open and assigns the
  reduced structure to its closure. No reducedness of P is assumed.
- X itself may be nonnormal. There is no normalization in the signature, and
  no geometric-integrality, projectivity, separatedness, finite-type, or
  algebraic-closure assumption.
- Every field characteristic is allowed. The size of H is independent of the
  schemes' universe, and finiteness uses `Finite`, not an enumerated `Fintype`.
- The identity element and noncommuting h,g obey the left action convention:
  Spec uses rho(h⁻¹), while a, A, b, aT use the same Aut multiplication.

Searches for an existing complete statement (2026-10-24):

- `msearch.py leanfinder` query: "Schematic image of invariant integral open in
  a Noetherian scheme inherits action and isomorphism on generic stalks".
  Eight hits: integrality of nonempty opens, integral section rings,
  `isIntegral_of_isOpenImmersion`, germ injectivity, domain stalks and an
  unrelated invariant ring theorem. No complete match.
- `msearch.py loogle` query:
  `AlgebraicGeometry.Scheme.Hom.image, AlgebraicGeometry.Scheme.Hom.stalkMap`.
  Zero hits.
- `msearch.py grep` query:
  `image.*[Ii]ntegral|[Ii]ntegral.*image|ker.*[Aa]ut`, directory
  `AlgebraicGeometry`. Three hits concern integral morphisms rather than the
  invariant integral schematic closure. No match.
- `msearch.py leansearch` query: "Schematic closure of an invariant integral
  open subscheme and canonical generic stalk isomorphism". Eight hits include
  `Scheme.Opens.stalkIso`, open-immersion stalk isomorphisms,
  `morphismRestrictStalkMap`, and `IsClosedImmersion.instIsIsoSchemeToImage`.
  These provide individual ingredients, not the node's full statement.
- `rg` in both project roots for the node id, invariantIntegralOpen,
  invariant_integral_open, schematic closure, and schemeTheoreticImage_reduced:
  found the reduced-schematic-image theorem and unrelated closure constructions;
  the semilinear Chow theorem uses the present result's ingredients but has
  substantially different properness/projectivity hypotheses and conclusions.
  No exact match. `grep -rn` of the node id in WeilConjectures returned no hits.
- `rg` for the proposed declaration name in Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json`: no collision.

Sources read: the item's complete seven-step proof and all its statement
and proof dependency records; Stacks `morphisms.tex` at
`lemma-scheme-theoretic-image-reduced` (056B),
`lemma-quasi-compact-scheme-theoretic-image` (01R8),
`lemma-factor-factor`, `lemma-integral-scheme-rational-functions` (01RV), and
`definition-function-field` (01RW). These support the node as written.
No STATEMENT-DISPUTED flag or node fault was found.

Validation: `scompile.py NE lem-sfb-invariant-integral-open-schematic-closure`
compiled this module cleanly in both sandbox and library modes on the server.
No compiler errors or warnings were reported. All universes and variables are
explicit; both auto-implicit options are disabled. The JSON signature is taken
verbatim from the theorem keyword through the final type, excluding `:=`.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
