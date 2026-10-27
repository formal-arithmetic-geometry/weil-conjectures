## Worker report

The module `Sheaf.AlgebraicGeometry.TraitLineSectionGenericGermsExtension` states
`AlgebraicGeometry.trait_line_section_generic_germs_extension`, with `sorry`.
The canonical generic open is written directly using Mathlib
as `f ⁻¹ᵁ PrimeSpectrum.basicOpen π`, without defining a second named wrapper. One auxiliary
definition constructs the generic restriction of the given section, using
existing restriction, direct image, and restriction-section isomorphisms.
It belongs to this node's canonical maps, is listed in `lean.declarations`,
and has real data. There are
no new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- The DVR is `{R : Type u} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`; the uniformizer is `(π : R)
  (hπ : Irreducible π)`. Mathlib's `irreducible_iff_uniformizer` identifies
  this with generation of the maximal ideal.
- `f : Y ⟶ Spec (.of R)` supplies the displayed base. `[Flat f]`,
  `[LocallyOfFiniteType f]`, and `[QuasiCompact f]` are exactly flat finite type.
- The special fibre is Mathlib's actual `f.fiber (IsLocalRing.closedPoint R)`.
  It uses the canonical residue field of the maximal ideal, which is
  canonically R modulo its maximal ideal. Its hypotheses are `IsReduced` and
  `hpure : ...IsPureDimension 1`. The latter quantifies over all irreducible
  components with their subspace Krull dimensions, and includes the empty fibre.
- `M : Y.Modules` with `[M.IsInvertible]` is the recorded invertible module.
  No separate quasi-coherence assumption is added: invertibility implies it.
- `f ⁻¹ᵁ PrimeSpectrum.basicOpen π` is the inverse image of `PrimeSpectrum.basicOpen π`.
  For a DVR this is the canonical open image of base change to the fraction
  field, since R[1/π] is its fraction field. Thus the statement is independent
  of a choice of isomorphic fraction-field model K, and the special-fibre
  model is independent of a choice of residue-field model k. The named K and
  k in the prose are not additional assumptions or data on which the result
  depends. `hU : (f ⁻¹ᵁ PrimeSpectrum.basicOpen π) ≤ U` is exactly containment of Y_K.
- `sU : Γ(M, U)` is the given section; these are exactly sections of M|U.
  `traitLineGenericSection` restricts it to the generic open and identifies
  that section with a global section of J = j_*(M|Y_K) on Y. The definition
  uses `restrictAppIso.inv` and restriction along the actual image inclusion;
  there is no choice, arbitrary comparison map, or existence axiom.
- `hintegral` quantifies over every `Z ∈ irreducibleComponents` of the actual
  special fibre and every `η` satisfying `IsGenericPoint η Z`. Its ambient
  point is `f.fiberι ... η`, not an assumed point of U. The left member is the
  germ at that point of the global section of J just constructed. Membership
  in `Set.range` of the stalk of the restriction-adjunction unit says precisely
  that this germ is in the image of M_eta. For a quasi-coherent module this
  target J_eta is canonically M_eta[1/π]. Indeed, on affine neighbourhoods
  sections on D(π) are module localization (the imported Tilde localization
  declarations), and taking the filtered colimit over neighbourhoods commutes
  with localization. The canonical unit sends a germ to that same germ with
  denominator one. This is a canonical model for the localized stalk, not a
  stronger hypothesis that local extension is already supplied.
- The first conjunction is `∃! s : Γ(M, ⊤), ... = sU`; the displayed map is
  restriction to U. It states existence and uniqueness of the extension.
- The second conjunction quantifies over every `V : Y.Opens` and asserts
  `Function.Injective` of restriction to `V ⊓ (f ⁻¹ᵁ PrimeSpectrum.basicOpen π)`.
  There is no affineness or quasi-compactness assumption on V.
- The third conjunction supplies `(W : Y.Opens) (hUW : U ≤ W)
  (sW : Γ(M, W))`, and the equality of its restriction with sU. For each
  special-fibre component generic point it supplies its membership `hηW`
  in W and asserts that the germ of sW equals every integral lift `t` of the
  given localized generic germ. Thus the section agrees with the integral
  germs and glues with sU; the integral lifts are not discarded or replaced
  by unconstrained stalk elements.
- For every `y ∉ W` it asserts `(2 : ℕ∞) ≤ IsLocalRing.depth` of the local
  ring as a module over itself, and the same for the actual module stalk.
  The existential `hfinite` only supplies the finite-module instance needed
  by the recorded depth API; it is in the conclusion and is automatic for
  a rank-one stalk. The explicit `@IsLocalRing.depth ... hfinite` avoids a
  hidden `let` and uses the canonical stalk module action from Mathlib.
- There is no normality, integrality, properness, smoothness, nodal, marking,
  or connectedness hypothesis, and there is no nonemptiness hypothesis.

The original node is copied with only its `lean` field changed. Its six-step
proof is fully reproduced in the theorem docstring. Proof-only imports are
ordinary imports; statement interfaces are public imports.

Dependency interfaces read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (field extensions); the canonical
  fraction/residue field models are used as described above rather than adding
  field variables unused by the conclusion.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Sheaf.AlgebraicGeometry.PureDimension`:
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`: existing module-stalk
  carrier and maps; the underlying germ and induced stalk map in the signature
  are Mathlib's `TopCat.Presheaf.germ` and `stalkFunctor.map` on the canonical unit.
- The recorded, available proof declarations are imported from
  `WeilConjectures.AlgebraicGeometry.GenericFibreAffineRingModels`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, and
  `WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`:
  `generic_fibre_affine_ring_models`,
  `Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen`,
  `Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen`, and
  `Scheme.isIso_restrictAdjunction_unit_of_depth_two`.
  The proof dependency `lem-sfb-flat-curve-line-depth` has no recorded Lean
  declaration in the read clone and is therefore not imported; no use of it is
  needed to type this statement.

Edge cases checked before writing: Y empty (all point quantifiers empty and its
section module is zero); empty special fibre (the generic open is all of Y,
so U = Y and W = Y is possible); U = Y; U equal to the generic open; V empty;
non-affine and non-quasi-compact V; reducible or disconnected reduced special
fibre; generic points outside U. A test model Spec R[t] confirms why the
special generic points must be added to W before asserting depth two on the
complement. The nodal model R[x,y]/(xy-π) is included without a normality or
smoothness binder. These checks found no node fault or disputed statement.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "A line bundle section extends from the generic
  fibre of a flat scheme over a DVR if integral at generic points of a reduced
  pure dimension one special fibre"`: eight hits, including
  `Flat.generalizingMap`, valuative-square domain/fraction-ring declarations,
  and integral-scheme function-field/germ-injectivity declarations; no match.
- `msearch.py ... loogle '"AlgebraicGeometry", "germ"'`: twelve hits, including
  structure-sheaf germ maps and ringed-space stalk-map identities; no extension
  theorem for the present hypotheses.
- `msearch.py ... grep 'hartog|depth.*section|section.*generic.*fibre'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of project `lean/Sheaf` and `lean/WeilConjectures` for generic germs,
  localized stalks, trait line sections and the node id: no exact match.
  Existing rational-section and generic stalk results assume integral schemes;
  the nodal pullback theorem is a consumer and imposes extra nodal data.
  Existing Hartogs states extension after depth is assumed, rather than the
  integral-germ criterion and derived boundary depths of this node.
- The example CompactObject module is now withdrawn with no declarations; its
  node has been rebound upstream. The new module follows the required module,
  public-section, docstring, import, naming, and width conventions directly.

## Second reading by Q24

The dispatcher brief explicitly assigns a single worker, forbids starting other
agents, and places independent review with the maintainer. Accordingly this is
an in-thread second pass, not a claim that another worker reviewed the file.
I reread the node against the signature clause by clause as listed above. The
key checks were that special generic points need not lie in U, the germ is of
the global generic-direct-image section, every integral lift is retained in the
W clause, all opens V are quantified, and both depths use the recorded API.
Compiler feedback prompted explicit use of `M.val.presheaf` in the module-stalk
action and `(R := Y.presheaf.stalk y)` for the local-ring depth. No mathematical
statement was changed.

## Repair of return on head 39480c8457e3

The returned collision was `AlgebraicGeometry.traitLineGenericOpen`, also
indexed in `Sheaf.AlgebraicGeometry.TraitLineSectionOrderNormalization`.
Removed the duplicate definition and its entry in `lean.declarations`.
An attempted public import of the indexed owner could not resolve:
`scompile.py --source Sheaf.AlgebraicGeometry.TraitLineSectionOrderNormalization`
reported `Module source unavailable`, and both the compile and dry run confirmed
that its `.olean` does not exist on the server. The current DAG record of
`lem-sfb-trait-line-section-order-normalization` also has no Lean declaration.
Therefore every occurrence now directly uses Mathlib's existing canonical
construction `(f ⁻¹ᵁ PrimeSpectrum.basicOpen π)`. There is no renamed wrapper,
second definition, or copied theorem, and no unavailable import. The theorem
signature is updated verbatim in `lean.statement`; expanding the old wrapper
changes no mathematical hypothesis, conclusion, generic section, or edge case.
The original clause-by-clause reading applies with that expansion throughout.
