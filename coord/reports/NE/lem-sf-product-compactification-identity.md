## Worker report

The delivery states `AlgebraicGeometry.ProEtale.ProductCompactification.product_compactification_identity`
in `lean/Sheaf/SixFunctors/ProductCompactificationIdentity.lean`. Its sole theorem has proof
`sorry`. All other declarations are concrete composites of existing functors, arrows and
isomorphisms, the two compactification records, the assertion packaging, and an elementary
instance exposing the existing quasi-compactness cancellation lemma. No node statement,
dependency list or proof plan is changed. There are no new nodes or dependency repairs.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors/`
`sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`, the symmetry paragraph,
especially “after reduction to proper f,g by the independence of the compactification”.
The item is the accepted four-step expansion of precisely that reduction. I also read its
resolved stage-1 re-split repair note; the delivery preserves that split. The recorded
CompactObject example module has now been withdrawn, so its header cannot serve as a
current example; I followed module mode and the current published normalization module.

Hypotheses, objects and clauses, matched individually:

- The finite field, distinct primes and coefficient context are `D : FiniteFieldDatum`,
  `C : D.CoefficientDatum`, `E : Type u` with `Field E`, `Algebra (Padic C.l) E`, and
  `FiniteDimensional (Padic C.l) E`. The positive exponent is `n` with `hn : 1 ≤ n`.
  These are the identical binders used by the recorded `SixFunctorDatum` declaration.
  Inside `Assertion`, `A₀` is `ULift (Padic.coefficientExtensionRing C.l E n)`; its
  finiteness comes from `Padic.finite_coefficientExtensionRing`. The lift changes the
  coefficient presentation, not the ring or its positive exponent. The datum retains
  all four coefficient stages and their completed/rational/common-stage conventions;
  the asserted identity, like the node's displayed identity, is at finite coefficients.
- The required six-functor datum is the binder `S : SixFunctorDatum D C E n hn`.
  Its finite operations are normalized against the fixed-scalar operations used below:
  `SixFunctorOperationDatum.finiteExchangeProjection` explicitly uses precisely the
  existing `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and
  `projectionMapOfCompactification`, conjugated by `sixFunctorFiniteRealization`.
  Thus these are its specified arrows, rather than freely supplied exchange/projection data.
- `B X Y Xb Yb : SixFunctorSpace D` are finite-type schemes over the specified field.
  The five `IsSeparated ...obj.hom` instances impose the node's separated scheme setting.
  `j : X ⟶ Xb`, `k : Y ⟶ Yb` are over-field maps, their `IsOpenImmersion` instances
  give the two open immersions, and `a : Xb ⟶ B`, `b : Yb ⟶ B` have `IsProper` instances.
  Consequently `f = j ≫ a` and `g = k ≫ b` are exactly the two compactified morphisms.
  The order is Lean's left-to-right composition, so `j ≫ a` is the node's `aj`.
  These arrows are separated and finite type in this setting. No properness is imposed
  on f or g themselves, and the opens need not be dense.
- The existing `OpenExternalTensor.Diagram j.hom.left k.hom.left T Tb` retains the
  product-open map `d.u`, four projections `d.p,d.q,d.pb,d.qb`, and both intermediate
  factorizations. `barSquare` identifies `Tb` as `Xb ×_B Yb`; `square` identifies `T`
  as `X ×_B Y`. The diagram's `right` and `left` equations identify the composites.
  Thus its raw schemes need no additional finite-type/separated binders: the two
  pullback assertions identify them with the products of the already specified schemes.
  The map t is written `d.q ≫ k.hom.left ≫ b.hom.left`; the other description follows
  from `square.w`. The map c is `d.qb ≫ b.hom.left`.
- `K` and `L` belong to the recorded `finiteTorConstructibleCategory` on X and Y.
  `K₀` and `L₀` are their inverse images under the recorded realization equivalence.
  This retains arbitrary bounded constructible finite-Tor inputs without choosing
  lattices, imposing perfection, or requiring a new constructibility predicate.
- F and G are the objects of the existing compactification-support functors at K₀,L₀.
  `OpenExternalTensor.inside A₀ d K₀ L₀` is exactly
  `p^* K₀ ⊗ q^* L₀`, hence the node's D. The tensor and pullback in these coordinates
  are `FiniteOpenProduct.tensor` and `.pull`, themselves the recorded derived tensor
  and exact constant-coefficient inverse image with its left-derived identification.
- `psi` is exactly the displayed Ψ: `sigma(F,G)`, then `projection cg L F`, then
  `S_g.map (sigma L (g^* F))`. Both signed symmetries are retained, in their prescribed
  places, using the published K-flat Koszul symmetry `FiniteOpenProduct.sigma`.
- `exchange` is the specified chosen-compactification shriek base-change arrow;
  `leftDerivedUpperStarIsoMapDerivedCategory` changes only inverse-image coordinates.
  `projection` similarly changes the target of the recorded projection map into
  exact inverse-image coordinates. It does not replace that map by an arbitrary iso.
- `chain` is Ψ followed by `S_g.map (tensorMap exchange (id L) ≫ PF_q)`.
  It uses the actual base-changed compactification `cf.ofIsPullback square` of q.
  `lambda` follows this by `compositor`, hence has exactly the node's α after that chain.
  `compositor` evaluates the recorded `coherenceProEtaleCompositor`, transporting its
  input along an étale-origin presentation and its inverse. It is the compositor
  normalized in `thm-sf-comp-composition`, not an arbitrary map between the endpoints.
- `factorCompactification` constructs the actual records `(j,a)` and `(k,b)`.
  `productCompactification` constructs `(d.u,d.qb ≫ b)` and verifies its factorization
  using `d.right`. Properness of `d.qb` follows by base change from a using `barSquare`.
- `properLambda` is λ_{a,b} on `j_!K₀,k_!L₀`: the same pair of signed symmetries,
  the canonical direct-image exchange mate, the two direct-image projection mates,
  and the inverse of `finiteDirectImageComposition` for the final proper composition.
  It is defined in proper direct-image coordinates, as required by the displayed equation.
- `OpenExternalTensor.comparison A₀ d K₀ L₀` is literally the dependency's normalized
  canonical e_{j,k}; its source is the external product of the two zero extensions and
  its target is `u_! D`. The first conjunct of `Assertion` is exactly
  `lambda ... = properLambda ... ≫ Rc.map (OpenExternalTensor.comparison ...)`.
  Its endpoints use the same compactification candidates as the node's supplied
  comparisons: `Rf! = Ra_*j!`, `Rg! = Rb_*k!`, `Rt! = Rc_*u!`. Thus no arbitrary
  endpoint identification or equality only up to an unspecified isomorphism is used.
- The second conjunct is the actual refinement-compatibility square. For arbitrary
  compactifications `cx',cy',ct'`, their lambda is the tensor of the canonical source
  comparisons, followed by the original lambda and the canonical target comparison.
  `change` is boundary inverse, the existing etale common-refinement comparison, and
  boundary, conjugated by the given input presentation. Its comparisons are exactly
  the canonical comparisons characterized by `compactification_coherence`; they
  include identity refinements, composites, and comparisons via common refinements.
  Quantifying all compactifications expresses the node's compatibility through any
  common refinement, rather than requiring the chosen choices to admit a fixed
  direction of refinement.
- `Assertion` quantifies origin presentations `OK,OL,OM` and identifications `eK,eL,eM`
  *in its conclusion*. These evaluate the canonical witnessed comparison, not extra
  hypotheses on K,L. The finite-constructible origin theorem in the proof dependencies
  supplies such presentations, also for the external tensor by pullback/tensor
  preservation. The identity is asserted for every presentation, including the identity
  presentation when available. In particular it does not select an arbitrary comparison
  or restrict to a special etale lift. This follows the recorded compositors' witnessed
  domain, which is explicitly not the entire unbounded pro-etale category.

Dependency declarations read and used:

1. `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`, including its full
   A1–A6 fields and normalization inherited from the operation datum;
   `Sheaf.Paper.SixFunctorOperationDatum`: `.finiteExchangeProjection`;
   `Sheaf.Paper.SixFunctorOperationDatumStages`: `SixFunctorSpace`,
   `sixFunctorFiniteRealization`, finite support/composition/proper/open normalizations.
2. `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
   `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, `.exchange`,
   `.compactExchange`, `.projection`. Its docstrings specify the same finite composites.
   The concrete finite declarations it documents and the operation datum records are
   `ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`,
   `ProEtale.projectionMapOfCompactification`, and `ProEtale.derivedBaseChangeMap` in
   `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.*`.
3. `Sheaf.Paper.SixFunctorDualNotation`: the recorded `.finiteCoefficientDual` signature
   and docstring were read. This identity uses its projection notation rather than a
   dual object: the module explicitly directs finite PF to the same concrete declaration
   used above. The module is publicly imported as the statement dependency requires.
4. `Sheaf.SixFunctors.OpenExternalTensorNormalization`:
   `AlgebraicGeometry.ProEtale.OpenExternalTensor.Diagram`, `.inside`, `.comparison`,
   `.FiniteAssertion`, and `.finite_open_external_tensor_normalization`. I read their
   signatures and constructions, including opposite factorization and signed symmetry.
5. Proof imports: `Sheaf.Paper.ExchangeFunctoriality`,
   `Sheaf.Paper.ProEtaleConstructibleOrigin`, `Sheaf.Paper.CompactificationCoherence`,
   and `Sheaf.Paper.CanonicalOriginCompactSupportComposition`. The latter's
   `originComposition` and its witness adapters identify the retained compositor.
   The existing `coherenceProEtaleCompositor`, `coherenceBoundaryComponent`, and
   `coherenceEtaleChangeIso` from `Sheaf.Paper.CompactSupportSiteCoherence` implement
   its evaluation and comparison. The first/second-open substitution nodes and
   `prop-sf-pf-coherence` have no recorded Lean declaration yet, so no import is possible
   for those three; the theorem docstring retains their separate roles in all four steps.

Edge cases checked before writing and again against the compiled signatures:

- j or k an identity, including both identities: their candidates remain the specified
  records, rather than replacing a canonical map by an unconstrained identity. The
  open normalization and direct-image identity unitors give the usual identity case.
- Empty schemes and empty product: no nonemptiness or denseness hypotheses occur;
  all functors and the same equation are defined.
- K or L zero: all terms are the same functorial composites, with no nonzero input
  assumption. Arbitrary shifts, including odd degrees, retain the two Koszul symmetries.
- n=1 is permitted by `1 ≤ n`; no hidden exponent shift occurs. All universe binders
  are explicit; schemes and E have universe u and coefficient sheaves use the
  published u+1 coefficient universe via ULift.
- Arbitrary original compactifications and identity/common refinements occur in the
  second conjunct, rather than a selected presentation or only a comparison iso.
- Quasi-compactness of f and g is derived from the finite-type structure maps using
  `QuasiCompact.of_comp`, and that of q by base change. None is an extra theorem binder.

Searches performed (all msearch calls use group NE and this item):

- LeanSearch: `Compatibility of compact support Kunneth composite with product compactification`:
  eight hits about compactly supported functions and composition, none about the six-functor map.
- LeanFinder: `The compact support Kunneth map defined by exchange and projection agrees with proper external products after compactification`:
  eight hits including `CompactlySupportedContinuousMap.compLinearMap`, condensed/CompHaus
  comparisons and `LightCondensed.ihomPoints_symm_comp`; none states this identity.
- Loogle: `"projectionFormula", "comp"`: zero hits.
- msearch grep: `compactification|kunneth|Kunneth` under Mathlib/CategoryTheory: zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf/Paper` for
  `lem-sf-product-compactification-identity|productCompactification|product_compactification|kunneth|Kunneth`:
  found the existing relative Kunneth isomorphism, supported-product comparisons,
  open-product normalization and ordinary Kunneth infrastructure. Reading these
  distinguished mere existence/isomorphism statements and other supported products
  from this specified equality. The open normalization is reused, not redefined.
- rg of both source trees and `dag/lean_names_upstream.json` for the proposed namespace,
  theorem and helper names found no existing declaration at those full names.

Validation: all compilation uses the prescribed scompile.py, never lake or a global build.
Initial helper-only compile passed. The complete compile found compactification proof fields
and missing inferred quasi-compactness; these were repaired using the existing field and
base-change APIs. A subsequent compile passed typing but reported style warnings on a
class-valued proof definition; it was changed to a named instance and the unnecessary
haveI was changed to have. The final compile and delivery preflight results are recorded
below after they complete. No mathematical statement fault or STATEMENT-DISPUTED remains.

Final scompile result: both sandbox and library module passed with no errors or warnings
(11.1 s and 7.5 s). The prescribed delivery dry run passed preflight and compilation,
printing `OK (dry run): commit e47b2db835a passes the preflight and compiles; nothing pushed`.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
