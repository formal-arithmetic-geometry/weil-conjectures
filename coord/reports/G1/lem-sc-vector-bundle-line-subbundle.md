## Worker report

The module states `AlgebraicGeometry.exists_saturated_line_subbundle`. It binds an integral,
Noetherian scheme `X`, regular local stalks and dimension-one non-generic stalks, a positive
rank `r`, a finite locally free module `E` of rank `r`, and a nonzero generic-stalk element `s`.
Its conclusion exhibits `L,Q`, maps `ι,π`, their zero composite, invertibility of `L`, finite
local freeness of `Q` of rank `r-1`, and short exactness of the resulting complex. The
`IsIntegral` dependency is Mathlib's `AlgebraicGeometry.IsIntegral`; the function-field
notion is imported from `Sheaf.AlgebraicGeometry.FunctionField` as
`AlgebraicGeometry.Scheme.functionFieldOfComponents`; invertibility is
`AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`.

The edge cases checked were `r=1` (the quotient rank is `0`), nonzero `s`, and the generic
point versus non-generic points in the dimension hypothesis. Searches used the supplied
LeanSearch (service unavailable), LeanFinder/Loogle (no subbundle declaration), and Mathlib
and project `rg` searches (no matching theorem). The statement is left with `sorry` as
required for stage 2.

## Earlier second reading (a previous round; superseded)

Reading the node and file together: `X`, integrality, Noetherianity, regularity, dimension one,
`r≥1`, finite local freeness, and nonzero generic element are all represented by binders. The
conclusion explicitly gives an invertible line object, a rank `r-1` locally free quotient, and
a short exact sequence. The generic stalk element is represented by the stalk carrier at
`genericPoint X`; the function field is the corresponding generic stalk supplied by the
recorded function-field declaration. No declaration is proved beyond the required `sorry`.

## Second reading by G1

Read the item node, all three statement-dependency nodes and their actual declarations,
and the entire delivered module. The source blueprint is absent from this read-only
clone, so I read the complete `lem-sc-riemann-roch.md` on the project server over SSH,
including its preliminaries and the proof of (*). This is the node's source, rather than
an independent Stacks theorem about subbundles: Stacks 0BS6 there supplies line-bundle
Riemann–Roch, not the saturation argument. I also read the Stacks integral-scheme and
function-field definitions in properties.tex and morphisms.tex on the server.

Objects, hypotheses and conclusions, item by item:

- Scheme X: `(X : Scheme.{u})`; matches, with an arbitrary universe u.
- Integral and Noetherian: `[IsIntegral X] [IsNoetherian X]`; matches. Read Mathlib
  Properties' nonempty/domain fields and Noetherian's locally Noetherian plus compactness
  definition. No base field, algebraic closure, smoothness or properness is added: the
  source's local argument only uses the abstract regular integral Noetherian curve
  assumptions explicitly extracted by this node.
- Regular: `hregular` asserts IsRegularLocalRing for every structure-sheaf stalk;
  matches the node's regularity, with no extra finite-type or separated assumption.
- Dimension exactly one: `hdim : topologicalKrullDim X = 1`; matches. Read the definition
  as Krull dimension of irreducible closed sets. Replaced the former condition that
  non-generic stalks have dimension one: it was vacuous on a field spectrum and thus
  admitted dimension zero, which the node does not.
- Generic point and K: `genericPoint X` and `X.functionField`; matches. Read the
  function-field node and its recorded module: its integral-scheme clause expressly
  reuses Mathlib Scheme.functionField, the structure stalk at genericPoint X. The
  component-product definition is for the other clause and is not used here. Removed
  its unused import; kept Mathlib.AlgebraicGeometry.FunctionField.
- Rank and vector bundle: `(r : ℕ) (hr : 1 ≤ r)` and
  `(E : X.Modules) [E.IsFiniteLocallyFreeOfRank r]`; matches. Read the upstream
  LocallyFree declaration: a covering by restrictions isomorphic to the Fin r free
  module, giving exactly finite local freeness of constant rank.
- Every nonzero s: `(s : ↑(TopCat.Presheaf.stalk E.val.presheaf (genericPoint X)))`
  and `(hs : s ≠ 0)`; matches. The scalar action is the existing module-stalk action
  from Mathlib.Algebra.Category.ModuleCat.Stalk, not a new assumption or private copy.
- L is the specified kernel for s: the forall-x Set.range equality says the inclusion
  stalk image is precisely the preimage of `Submodule.span X.functionField {s}`
  under the existing stalkSpecializes map from x to the generic point; matches.
  Indeed every neighborhood of x contains eta, so the stalk of the generic-point
  pushforward quotient is E_eta/Ks. Its kernel stalk is exactly this preimage.
  ShortExact makes the inclusion monic. Subsheaves are determined by their stalk
  subobjects, so this condition specifies the node's kernel uniquely up to the
  canonical isomorphism over E, rather than allowing an arbitrary line subbundle.
  No new notion/definition node or dependency module is required for this rendering.
- Invertibility: `L.IsInvertible`; matches the recorded Scheme.Modules.IsInvertible,
  whose neighborhood trivializations to the structure sheaf imply rank-one local
  freeness and quasi-coherence. It is not SheafOfModules.IsInvertible.
- Generic fibre Ks: the final Set.range equality at genericPoint X is exactly
  `Submodule.span X.functionField {s}`; matches. This clause was absent before.
- Quotient and rank: `Q.IsFiniteLocallyFreeOfRank (r - 1)` together with
  `ShortComplex.ShortExact (ShortComplex.mk ι π hcomp)`; matches. ShortExact says π
  is an epimorphism with kernel the monic inclusion ι, so Q is E/L up to canonical
  isomorphism, not an unrelated locally free module. The witness hcomp now actually
  supplies the zero-composite argument to ShortComplex.mk.
- Exact sequence: the same ShortExact clause supplies precisely 0 → L → E → Q → 0;
  matches. The quantifiers choose this saturation and quotient after the specified s.

Edge cases: r=1 gives rank-zero Q and L=E (the generic line is the whole generic
fibre); r=0 is explicitly excluded by hr exactly as in the node. Zero E has no nonzero
s under the given rank hypothesis. Empty schemes are excluded by IsIntegral, not by
an added assumption; a dimension-zero field spectrum is now excluded by hdim. No
index set is chosen or required nonempty. There is no characteristic assumption.
The arbitrary scheme universe is preserved, and stalks are the existing module-stalk
carriers, with no unbound variables or extra module/field instance binders.

Independent searches: LeanSearch query “saturation of a rational line in a vector bundle
on a regular one dimensional scheme” returned HTTP 500 (unavailable, no mathematical
verdict). LeanFinder query “prescribed rational section saturated invertible subsheaf
regular curve” returned fraction/local-section declarations and ModuleCat.Tilde.sectionsSubmodule,
none stating this result. Loogle query “stalkSpecializes” returned no recognized identifier.
I searched `saturated|line.subbundle|saturation` with rg across Mathlib AlgebraicGeometry,
upstream WeilConjectures, and project lean/Sheaf: only unrelated saturation constructions
and the local DVR saturation lemma, not this sheaf theorem. Read Mathlib's stalkSpecializes
signature (specialization from eta to x gives E_x → E_eta) and the existing module-stalk
construction, as well as the project's invertible_module_generic_stalk declaration.
No existing declaration supplies the full requested theorem.

Mismatches repaired: the earlier theorem chose an arbitrary subbundle independent of s
and omitted the kernel/saturation characterization and generic-fibre equality. Added
both using existing stalk maps and span. Replaced the dimension hypothesis as above,
fixed the ShortComplex.mk proof argument, and used explicit coerced module-stalk carriers.
Added the standard copyright header; removed the unused component-function-field import;
expanded the theorem docstring to all four DAG proof steps with the named dependencies.
No DAG statement correction, new node, dependency module, or definition is needed; the
node's mathematical statement is unchanged. No theorem was proved: the sole proof is
sorry, and no definition contains sorry. Single-file server compilation passed cleanly
(no errors or warnings). The node lean.statement is the literal signature from the file.
