## Worker report

Item: lem-sf-continuous-adic-proper-base-change-restriction. The module
Sheaf.Paper.ContinuousAdicProperBaseChangeRestriction states proper base change for the
ordinary sectionwise module-derived operations and the specified restriction map. Every
postponed proof is a named theorem with the source and proof plan in its docstring. The
main declaration is
AlgebraicGeometry.ProEtale.ContinuousAdicRestriction.proper_base_change_restriction.

Clause-by-clause rendering:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  `hc : ringChar k ≠ 0` is positive characteristic; `l : ℕ` with `[Fact l.Prime]`
  is the prime, and `hl : l ≠ ringChar k` is its required inequality.
- The chosen algebraic closure with the extended topology is the existing `PadicAlgCl l`.
  `PadicAlgCl.locallyFiniteFunctions l U.left` is exactly continuous functions whose
  values have locally finite-dimensional Q_l span. Its definition quantifies over every
  point and a neighbourhood with finite-dimensional span. `coefficientPresheaf` packages
  its pointwise commutative rings; its restrictions use the existing
  `locallyFiniteFunctionsCompAlgHom` and `WeilCoefficients.uliftAlgHom`.
  `coefficientPresheaf_isSheaf` states descent, so `coefficientRing` is the already-sheaf
  representative of the required sheafification, canonically the same sheaf. ULift changes
  only the coefficient universe, not functions or topology.
- Every site is `Scheme.ProEt.topology X`, on the original small site with objects in
  universe u+1 and morphisms in u. No equality of these universes is imposed.
- `coefficientMap` is literally precomposition with `pullback.fst U.hom f`. Its
  naturality theorem is the projection equation for pullback.map. `direct` is Mathlib's
  `SheafOfModules.pushforward` with this ring action. This is not a category of objects
  all descending to one finite stage.
- `proEtaleRingModules X R` is the recorded `ringedSiteModules`/`SheafOfModules` category
  of sectionwise modules. The derived categories are the ordinary `DerivedCategory`,
  with the recorded standard localization and K-injective resolutions from
  `ProEtaleOperations`. `Functor.rightDerivedFunctor` is its ordinary total right derived
  direct image. It has the same universal pair as the recorded
  `rightDerivedFunctorOfQuasiIsoResolutions`; the stronger monomorphic-resolution
  infrastructure is supplied by the module categories, not assumed of M.
- `[T.Over (Spec (CommRingCat.of k))]`, the locally finite type and quasi-compact
  assumptions on its structure map say that T is finite type over k. `(p : P ⟶ T)` with
  `[IsProper p]` says proper; no separatedness of T is assumed. P receives the composite
  structure map to k, so no independent k-structure or compatibility is required.
- `(h : T' ⟶ T) [IsImmersion h] [QuasiCompact h]` is the quasi-compact locally closed
  immersion. Mathlib's immersion class is equivalent to a closed immersion into an open
  subscheme. `pullback p h`, `pullback.fst p h`, and `pullback.snd p h` are P', h', and p'.
- `inverseRing h (coefficientRing l T)` and
  `inverseRing (pullback.fst p h) (coefficientRing l P)` are the actual inverse-image
  rings. `restrictedMap` gives the induced p' coefficient map: apply h inverse image to
  the p coefficient map and then the canonical ring-valued exchange.
- `proEtaleModuleInverseImage` is the dependency's actual topos inverse image of modules
  with transported action. Its codomain is modules over the actual inverse-image ring.
  No tensor extension to the separately named coefficientRing on T' or P' occurs.
  Its normalized adjunction has the actual model-site Kan-extension unit, explicitly
  checked on every section in `inverseAdjunction_existsUnique`.
- `hM` renders the whole local finite-partition hypothesis: for each point choose an open
  immersion j containing it; choose finitely many immersed strata indexed by `Fin n`;
  the `∃! a` condition partitions every point of U; on each stratum the inverse image
  along `i a ≫ j` has local generators q which are both locally free and finite type.
  These two properties of the same generators mean that their free presentation maps
  are isomorphisms with finite bases. Thus the module is pro-etale locally finite free
  over exactly the restricted coefficient ring, with rank allowed to vary.
- `directSquare_existsUnique` fixes the module direct-image square by equality with the
  existing underlying abelian `squareLowerStarIso`. The faithful forgetful functor makes
  this unique. `ordinaryExchange` is its mate for the two normalized pure inverse-image
  adjunctions. This is the ordinary counit adjunct in the node: transposing the same
  square along p' instead gives inverse-image composition followed by h' applied to the
  p-counit. It is not an unconstrained map between the right endpoints.
- `exchangeAux` applies the ordinary exchange on homotopy categories followed by the
  target derived unit. `exchange` uses `rightDerivedDesc` with the standard exact-right
  composition unit. This constructs the canonical derived restriction map on every
  derived object. On K-injective resolutions it is bc_I followed by p'_* of the
  replacement of h' inverse image of I, as in proof step 4.
- `degreeZeroExchange` evaluates on M[0] and uses the canonical exact-functor single
  comparison to identify the target with Rp'_*((h' inverse image M)[0]). `properExchange`
  specializes this construction to the specified geometric ring square. `IsIso` in the
  main theorem is therefore the requested derived isomorphism, not just per-degree
  cohomology isomorphisms.
- `degreeZeroUnit` is the ordinary total derived-unit comparison, via the existing
  `rightDerivedFunctorUnitQ` and the canonical single-complex identifications. The second
  conjunct of the main theorem is exactly Ex after h inverse image of delta_p equals
  delta_p' after bc[0]. The displayed single-functor comparison merely identifies
  h inverse image of (p_*M)[0] with (h inverse image p_*M)[0]. It is needed for typing,
  and adds no mathematical clause. `degreeZeroExchange_normalization` states the same
  unit equation generally.
- No Frobenius, compactification, common open, common finite stage, completion,
  connectedness or global constant rank is assumed.

Dependencies used: Mathlib's `Padic`, `AlgebraicClosure`/`PadicAlgCl`, `Scheme.ProEt`,
`IsProper`, `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsClosedImmersion`,
`IsImmersion`, `Limits.pullback`, `DerivedCategory` and `HasDerivedCategory`; the modules
Sheaf.CategoryTheory.RingedSiteModules (`CategoryTheory.ringedSiteModules`),
Sheaf.AlgebraicGeometry.ProEtaleInverseImage (`proEtaleSheafInverseImage`,
`proEtaleModuleInverseImage`, `proEtaleModelRingUnit`, `proEtaleModuleToModel`),
Sheaf.AlgebraicGeometry.ProEtaleOperations (`proEtaleRingModules` and its standard
localization/K-injective instances), and
Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions (the universal-pair
interface). The operations node is added to stmt_deps as an already-landed dependency.
The existing upstream Adic.Ring and Adic.ConstantSheaf supply the actual finite-span
functions; no replacement for those functions or their topology is introduced. All stated
proof-dependency modules are imported privately for the ten-step proof in the docstring.

Edge cases checked: empty P or T' gives zero module/derived categories; Fin 0 permits the
empty partition; finite-rank local generators permit rank zero and varying ranks; h the
identity yields the canonical identity exchange through the resolution identifications;
nonseparated finite-type T is retained; arbitrary module sheaves are allowed as intermediate
resolutions, with constructibility required only of M. Schemes, sites, module values,
local-generator indices and generic localization universes are explicitly bound.

Searches: prescribed msearch leanfinder query "Proper base change for continuous locally
finite dimensional algebraic closure l-adic module sheaves on the pro-etale site" returned
geometric base-change stability and light-condensed sheafification/monoidal declarations,
with no matching ordinary-module exchange. Loogle `"SheafOfModules", "pushforward"`
returned 12 presheaf pushforward and comparison declarations, with no proper derived
base-change result. Prescribed Mathlib grep `proper.*[Bb]ase[Cc]hange|locallyFiniteFunctions`
in AlgebraicGeometry returned stability under base change, not the statement. Repository
rg for locallyFiniteFunctions, continuousAdic, adicBaseChange and derivedBaseChange found
upstream Adic.ConstantSheaf, Ring, Module, Constructible and BaseChange. The latter's
`adicDerivedBaseChangeIso` assumes open immersion; it cannot state this item's closed
restriction cases. Generic bounded-below derived exchange exists in PlusBaseChange;
this module supplies the universal unbounded construction needed here. DAG searches for
locallyFiniteFunctions and locally finite-dimensional found the native Weil framework
and related realization items, but no matching sectionwise ordinary proper exchange.
The exact item-id search in upstream Lean found no declaration. Searches are also logged
in searches.jsonl in the sandbox. Source checked: Stacks proetale.tex,
label theorem-proper-base-change, and current blueprint
sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.md,
clause 3. Tag 09C9 is used as the finite-stage input, exactly as the node warns.

No statement correction or STATEMENT-DISPUTED flag is needed. The sole citer
lem-sf-weil-open-immersion-compact-image-extension-by-zero continues to receive the stated
ordinary proper exchange with the required restriction normalization.

## Second reading by NX

The dispatcher explicitly prohibits starting other agents; this is the worker's final
self-audit, with independent review left to the maintainer as the brief specifies.
Re-read the node and signature against the mapping above. The essential checks are the
actual inverse-image coefficient rings, pure inverse image rather than tensor extension,
the canonical map fixed by normalized mates, finite free rather than arbitrary locally
free ranks, the derived isomorphism, and the explicit delta normalization. The comparison
with upstream open base change exposed its insufficient open-immersion domain, so it was
not attached as an existing match. The signature retains positive characteristic,
prime-to-characteristic, properness, finite type and quasi-compact immersion hypotheses.
No statement fields were changed. Definitions have real data; unique-choice definitions
choose maps fixed by section/unit equations, not arbitrary maps or an arbitrary equivalence.

The canonical square uses the named type `DirectSquare` and predicate
`DirectSquareNormalized` to share its sectionwise normalization without repeatedly
expanding the ringed-site functors during kernel checking. This changes no data
or mathematical condition. Both helper declarations are included in `lean.declarations`.
