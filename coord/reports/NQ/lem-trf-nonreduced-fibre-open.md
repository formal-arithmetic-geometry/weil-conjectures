## Worker report

The module `Sheaf.AlgebraicGeometry.NonreducedFibreOpen` states
`AlgebraicGeometry.exists_nonempty_open_nonreduced_fibers_of_nonreduced_generic_fiber`
with proof `sorry`. Its source is Stacks Project, More on Morphisms, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, read in `literature/stacks-project/more-morphisms.tex`
at lines 7110–7161. The module and theorem docstrings name that source and blueprint node.
The theorem docstring gives all eight DAG proof steps, including the reduction of the base,
the denominator shrinkings, the annihilator exact sequence, both generic-freeness inputs,
and the residue-field injection. No definition or additional theorem is introduced.

The hypothesis and conclusion correspondence is:

| Node clause | Lean |
| --- | --- |
| Schemes Z and T and morphism h : Z → T | `{Z T : Scheme.{u}} (h : Z ⟶ T)` |
| h of finite type | `[LocallyOfFiniteType h] [QuasiCompact h]`, exactly the conjunction recorded by def-weil-finite-type-morphism |
| T irreducible | `[IrreducibleSpace T]`, including nonemptiness |
| Specified generic point ξ of T | `(ξ : T) (hξ : IsGenericPoint ξ (Set.univ : Set T))` |
| Scheme-theoretic generic fibre not reduced | `(hgeneric : ¬ IsReduced (h.fiber ξ))` |
| An open subset W of T | `∃ W : T.Opens` |
| W nonempty | `(W : Set T).Nonempty` |
| Every fibre above W is nonreduced | `∀ t : T, t ∈ W → ¬ IsReduced (h.fiber t)` |
| No flatness, Noetherianity or reducedness assumption on T | There are no such binders; no field, characteristic or integrality assumption is imposed either |

Every universe and variable is explicitly bound; `set_option autoImplicit` is not needed.
The common arbitrary scheme universe u is the universe of Mathlib's category of schemes and
its fibre construction. It does not constrain the base dimension, characteristic, size of a
cover, or its rings' finite-generation properties beyond finite type of h.

Statement dependencies use the following recorded declarations, with each source signature
and its docstring read in the pinned Mathlib:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`. Its recorded match
  `irreducibleComponents` uses `IsIrreducible`. The same file's `IrreducibleSpace` is the
  corresponding class for the whole underlying space, so no components or separate
  irreducibility notion are reconstructed.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, literally closure of
  the singleton equal to the specified set; the set here is the whole base.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, literally the pullback over the canonical residue-field
  point, with its recorded projections. No set-theoretic-fibre replacement is used.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, the sectionwise reducedness condition equivalent to the
  local-ring condition by `isReduced_of_isReduced_stalk` and `isReduced_stalk_of_isReduced`.

All statement-dependency modules are public imports. Recorded proof-dependency modules not
already public are ordinary imports, including
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`,
`Sheaf.RingTheory.GenericFiniteModulePresentation`,
`Sheaf.RingTheory.FinitelyPresentedAlgebraModuleGenericFreeness`, and the relevant Mathlib
function-field, pullback, localization, finite-type, free-module, tensor-product and flatness
modules. The reduction module was obtained with `scompile.py --source` because that current
upstream module was absent from the local source copy. The exact flat-quotient input is
`LinearMap.lTensor_injective_of_exact_of_flat` in `Mathlib.RingTheory.Flat.Equalizer`.
The remaining Mathlib proof declarations come from the imported modules named by the node;
no unstated proof dependency was manufactured or assumed.

Edge cases checked mathematically before writing:

- The empty base is excluded by the node's irreducibility hypothesis itself, not by an
  extra binder. The empty source has reduced empty generic fibre and cannot satisfy
  `hgeneric`, as required.
- Over a field, the dual-number source has nonreduced fibre and the only nonempty open of
  the one-point base works. No positive-dimensional-base assumption is present.
- A nonreduced irreducible base is permitted. For example the relative dual numbers over
  a dual-number base have nonreduced residue-field fibres. Conversely the identity on a
  nonreduced base has reduced residue-field fibres, so the generic-fibre hypothesis fails.
- Non-Noetherian domains are permitted; the proof plan uses the recorded 051T and 051S
  statements without a Noetherian hypothesis.
- For A = k[t] and B = A[x]/(x², tx), the generic fibre is reduced, so this example does not
  satisfy `hgeneric`; no unjustified claim about special nonreduced fibres is made.
- Every point of W is quantified, including nonclosed points, and every characteristic is
  allowed. No geometric-reducedness or perfect-residue-field hypothesis is substituted.
- The conclusion asks for a nonempty open, as the node does. It does not separately demand
  that ξ belong to it; that already follows from being a nonempty open in an irreducible
  space with generic point ξ.

Searches made with `msearch.py NQ lem-trf-nonreduced-fibre-open`:

- LeanFinder: `For a finite type morphism over an irreducible scheme a nonreduced generic
  fibre implies nonreduced fibres over a nonempty open subset`. Eight hits: reducedness,
  integrality and open-restriction criteria, no spreading theorem.
- Loogle: `AlgebraicGeometry.IsReduced, AlgebraicGeometry.Scheme.Hom.fiber`. One hit,
  `AlgebraicGeometry.instIsReducedFiberOfGeometricallyReduced`; read its source in
  `Geometrically/Reduced.lean`. It assumes geometric reducedness and concludes reducedness,
  so it is not the statement here.
- Grep: `nonreduced|nonReduced|generic.*[Rr]educed|[Rr]educed.*generic` in
  `AlgebraicGeometry`. One hit, the generic-stalk reducedness discussion in Properties,
  no matching theorem.
- LeanSearch: `Nonreduced generic fibre of a finite type morphism spreads to all fibres on
  a nonempty open irreducible base`. Eight hits, including `spread_out_of_isGermInjective`
  and uniqueness variants. These spread morphisms of stalks, not nonreduced fibres;
  reducedness/open-cover criteria are also returned. No exact match.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for `nonreduced`, `nonReduced`,
  `nonreduced_fiber`, `nonreduced_fibre`, and `nonreduced.*[Oo]pen`: no matching statement.
  The side library has unrelated nonreduced examples and comments.
- `rg` of the upstream source for the exact blueprint id: no hit.
- `rg` of `dag/lean_names_upstream.json`, Mathlib algebraic geometry, upstream and side Lean
  for the proposed declaration name and related open/nonreduced-fibre names: no collision.

There is no statement correction, disputed statement, new node or dependency module.
Only the original node's `lean` field is changed; its signature is copied verbatim from the
file and the date is from UTC. Initial `scompile.py` verification compiled both its sandbox
and library forms cleanly, in 2.1 seconds and 2.0 seconds respectively.

## Second reading by NQ

No second worker was started, as required by this dispatcher brief. The maintainer performs
the independent delivery review. As a final self-check, I reread the original node, the exact
source lemma and the Lean signature against the table above: both finite-type conditions,
the irreducible unreduced base, the specified generic point, ordinary scheme-theoretic fibre
nonreducedness, and the nonempty-open universal conclusion all agree. No mismatch requiring
a statement change was found, and no additional assumptions or conclusion clauses were added.
