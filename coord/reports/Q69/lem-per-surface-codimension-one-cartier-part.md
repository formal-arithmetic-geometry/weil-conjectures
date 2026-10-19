## Worker report

The module `Sheaf.AlgebraicGeometry.SurfaceCodimensionOneCartierPart` states
`AlgebraicGeometry.exists_surface_codimension_one_cartier_part` with one `sorry`.
No definitions, new nodes, or dependency repairs are needed. The natural-language
statement and every other field of the node are unchanged.

Hypothesis and clause correspondence:

- The scheme is `X : Scheme.{u}`, with arbitrary explicitly bound universe `u`.
- Integral is `[IsIntegral X]`, using the recorded Mathlib definition, which
  includes nonemptiness and domains of sections on nonempty opens.
- Regular is `hRegular : IsRegularScheme X`, exactly the recorded predicate
  `IsLocallyNoetherian X ∧ IsRegular X` (regular local stalk rings).
- Noetherian is `[IsNoetherian X]`, the standard locally Noetherian, quasi-compact
  scheme condition; its affine rings use the recorded `IsNoetherianRing`.
- Dimension two is `hDim : topologicalKrullDim X = 2`.
- A closed subscheme with its ideal is represented by `Z : X.IdealSheafData`.
  This is the existing affine-local quasi-coherent ideal data, not a new notion:
  its canonical `Z.subschemeι` is a closed immersion and its kernel is Z.
  `hZ : Z ≠ ⊥` means the closed subscheme differs from X. It permits the empty
  closed subscheme (`Z = ⊤`) and does not impose a morphism-properness hypothesis.
- The two existential ideals are `∃ L J : X.IdealSheafData`.
  `L.IsInvertible` is the recorded effective Cartier predicate: an affine-local
  nonzerodivisor generator. Both ideals are actual ideals inside the structure
  sheaf, rather than abstract invertible modules.
- `J.toModules.IsQuasiCoherentFiniteType` states exactly quasi-coherence and
  finite type using the recorded pqf-def-coherent declaration.
- The factorization is the equality `Z = L * J`, using Mathlib's multiplication
  of ideal data, whose affine ideals are the corresponding ideal products.
- The set T is directly `(J.support : Set X)`. Reading its definition shows that
  this is the zero locus of J on affine charts, equivalently Supp(O_X/J), not
  the support of J as a submodule. `range_subschemeι` identifies it with |V(J)|.
  No separate set parameter or arbitrary support choice is introduced.
- `Set.Finite (J.support : Set X)` is finiteness of T.
- For every `x ∈ J.support`, `IsClosed ({x} : Set X)` is closedness of that point
  in the ambient X, and `ringKrullDim (X.presheaf.stalk x) = 2` is the node's
  specified local-ring definition of codimension two.
- `(J.support : Set X) ⊆ Z.support` is containment in |Z|.
- There is no nonemptiness condition on T, and `L = ⊤` (the unit ideal) is
  permitted by the existential and the effective Cartier predicate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the scheme predicate
  is `AlgebraicGeometry.IsNoetherian` from Mathlib.AlgebraicGeometry.Noetherian.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`; global dimension is
  `topologicalKrullDim` from Mathlib.Topology.KrullDimension.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, through the existing canonical closed
  subscheme associated with ideal data; no duplicate predicate is written.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` (full signature read).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules` (the kernel of the
  canonical map to the pushforward of the structure sheaf of V(J)).

Recorded proof modules are imported, including the finite-type support theorem
and reduced-induced-closed-subscheme theorem. The Mathlib DVR and Noetherian
space modules supply the corresponding proof leaves. The genuine proof node
`lem-per-regular-prime-divisor-local-equations` has no Lean record or Mathlib
match yet, so no nonexistent module is imported; its use is preserved in the
proof docstring. It is a proof prerequisite, not a missing statement notion.
The seven-step docstring reproduces the supplied proof, with its local
prime-power division, colon-ideal gluing and finite closed support arguments.

Sources read locally: Stacks divisors.tex, lemma-codim-1-part (0AGB), full
statement and proof; resolve.tex, lemma-turn-into-effective-Cartier (0BIB),
statement and first proof paragraph. Their regular, nowhere-dense case gives
exactly the node's factorization. No statement correction is needed.

Edge cases checked mathematically before writing:

- The empty scheme is excluded already by integral and dimension two.
- Z empty: Z is the unit ideal; L = J = unit works and T is empty.
- Z Cartier: L = Z and J = unit works; T is empty.
- Z purely punctual: L = unit is allowed; on a surface the support is a finite
  set of codimension-two closed points.
- On Spec k[x,y], ideal (x^2 y^3) has unit residual; ideal x(x,y) has Cartier
  part (x) and residual (x,y); ideal (x,y)^2 has unit Cartier part.
- A two-dimensional regular local scheme is covered; neither a base field,
  finite-type-over-field hypothesis nor equidimensionality of divisors is added.
- Z = X is correctly excluded by `hZ`; there are no assumptions of excellence,
  ampleness, algebraic closure or projectivity.

Searches (2026-10-19, prescribed msearch.py wrapper):

1. LeanFinder: "On an integral regular Noetherian surface every proper ideal
   factors as an effective Cartier ideal times an ideal supported at finitely
   many closed codimension two points". Eight hits, principally
   Ideal.finite_mulSupport_coe, Ideal.finite_factors and other Dedekind-domain
   factorizations, plus Ideal.isLasker. None states the surface factorization.
2. Loogle: "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible,
   AlgebraicGeometry.Scheme.IdealSheafData". Zero hits; the search index does
   not know the upstream IsInvertible identifier. Its source was read directly.
3. Mathlib grep: "Cartier|codim.?1.*part", AlgebraicGeometry: zero hits.
4. LeanSearch: "A proper closed subscheme of a regular Noetherian surface is
   the product of a Cartier ideal and an ideal supported at finitely many
   closed points". Eight hits: IdealSheafData.subscheme/support/vanishingIdeal,
   support helpers and IsProper.mk. None is the required theorem. The search
   summaries incorrectly describe ideal-data support as support of the ideal;
   the actual source definition was read and takes the zero locus, as required.
5. rg on upstream WeilConjectures and side lean/Sheaf for the item ID,
   codimension/Cartier-part names and the proposed full declaration: no existing
   theorem. EmbeddedSurfaceCurveResolution only cites this item in its proof
   plan; CodimensionOneCostalkReduction constructs a different closure notion.
6. rg on dag/lean_names_upstream.json for the proposed theorem and surface
   Cartier names: no existing declaration. All statement dependency records
   and full recorded declarations/docstrings were read.

Validation: scompile.py compiled this file as both sandbox and library modules
successfully (2.8 s and 2.7 s respectively), with no diagnostics. Every variable
and universe is explicitly bound, and both auto-implicit options are disabled.
The sandbox contains only the item module, its lean-only node record and this
report (plus launcher brief markers).

The prior worker's stage-1 PASS is not a stage-2 Lean binding: the shared node
has reviewed.result = pass from Q48 but no lean field. This delivery supplies
only the missing stage-2 statement and preserves that split and review intact.

## Second reading by Q69

Author self-check, not an independent review: reopened the node and the Lean
file and checked every binder and conjunct against the correspondence above.
In particular `Z ≠ ⊥`, rather than `Z ≠ ⊤`, is the proper-subscheme condition;
J.support is quotient support; point codimension is local-ring dimension;
L and T are allowed to be unit and empty, respectively. No mismatch or
statement change was found. The maintainer's independent review remains the
independent second reading required by this remote-worker brief.
