## Worker report

The delivery states all clauses of lem-per-regular-lci-geometric-calculus in
Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus. Every theorem has proof `sorry`;
its docstring contains the corresponding natural-language node proof steps and sources.
The original statement, proof and proof dependencies are unchanged. The only node delta is
its Lean record and the addition of one general regular-closed-immersion definition.

Clause-by-clause correspondence (names are in namespace AlgebraicGeometry):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes and morphisms | Explicit `Scheme.{u}` binders and `⟶`; arbitrary universe `u` |
| Noetherian schemes throughout | `[IsNoetherian ...]` on every scheme quantified in the respective clause |
| Regular schemes | The recorded predicate `IsRegularScheme`, including local Noetherianity and regular stalks |
| Closed regular equations | `IsRegularClosedImmersionWithCodimension i c`; closed immersion and affine-local regular lists generating the section-map kernel |
| Codimension is the locally constant length and conormal rank | `regularClosedImmersion_codimension_rank_unique`: `IsLocallyConstant c`, equality with `Module.finrank` of the stalk-kernel `Cotangent` over the quotient local ring, and uniqueness against every other equation-length function `d` |
| An immersion between regular schemes is regular | `exists_regularClosedImmersion_factor_of_regular`: `[IsImmersion i]`, regularity of both schemes, and an open ambient `U` with a regular closed factor `j` satisfying `j ≫ U.ι = i` |
| Flat base change and unchanged codimension | `regularClosedImmersion_flat_baseChange`: `[Flat g]`, the canonical `pullback.snd i g`, with length `c ∘ pullback.fst i g` |
| Composition and additive codimension | `regularClosedImmersion_comp_codimension`: for `i : Z ⟶ Y`, `j : Y ⟶ X`, length `fun z ↦ c z + d (i z)` |
| Section of separated smooth map of relative dimension r | `regularClosedImmersion_smooth_section`: `[IsSeparated p]`, `[SmoothOfRelativeDimension r p]`, `hs : s ≫ p = 𝟙 S`, length constantly `r` |
| Smooth source over regular base is regular | `isRegularScheme_of_smooth_over_regular`: `[Smooth f]`, `IsRegularScheme X`, conclusion `IsRegularScheme Y` |
| Finite-type map of regular affines | `[IsAffine Y] [IsAffine X]`, `[LocallyOfFiniteType f] [QuasiCompact f]`, and `hY`, `hX` in `regular_affine_finiteType_closed_presentation` |
| Existence of closed embedding into affine space | First conjunct: `∃ r i`, where `i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) X`, its composite with the canonical projection equals `f`, and it is closed |
| Every such embedding is regular | Second conjunct quantifies every `r` and `i` satisfying that same over-X equality and closedness, and provides the sourcewise length `c` |
| Arbitrary regular-closed/smooth factorization of f | `i : Y ⟶ P`, `p : P ⟶ X`, `hi : i ≫ p = f`, `[Smooth p]`, the regular-closed predicate for `c : Y → ℕ`, and `r : P → ℕ` with `hr` identifying its values with fibre dimension at every point |
| Relative dimensions may vary on components | `hr : ∀ z, topologicalKrullDimAt (p.asFiber z) = (r z : WithBot ℕ∞)`; no global constant-dimension condition is imposed |
| Local constancy of r-c | First conclusion of `regular_lci_virtual_dimension_formula`: `IsLocallyConstant (fun y ↦ (r (i y) : ℤ) - (c y : ℤ))` |
| Integer dimension formula | For each `y`, natural-number witnesses `dx dy t` identify the two `ringKrullDim`s and the cardinal `Algebra.trdeg` with their finite values; `(r (i y) : ℤ) - c y = (dy : ℤ) - dx + t`. No natural subtraction, infinite-to-zero conversion, or hidden `let` is used |
| Canonical residue extension κ(f(y)) → κ(y) | `(f.residueFieldMap y).hom.toAlgebra` is passed explicitly to `Algebra.trdeg`; its `toModule` is passed explicitly to `FiniteDimensional` |
| Independence of factorization | `regular_lci_virtual_dimension_independent` quantifies two intermediates `P Q`, maps `i,p,j,q`, commuting triangles, codimension functions `c,d`, and fibre-dimension functions `r,s`; its conclusion equates both integer differences at every `y` |
| Quasi-finite / finite-type finite-fibre case | `finite_residue_extension_trdeg_zero_of_quasiFinite` accepts either the literal `LocallyOfFiniteType f ∧ QuasiCompact f ∧ f.HasFiniteFibres`, or the recorded `f.IsQuasiFinite`, and concludes finite-dimensional residue extension and trdeg zero at every source point |
| Zero codimension, zero relative dimension, empty schemes | All lengths are `ℕ` with no positivity binder. All pointwise conclusions quantify `y : Y`, with no nonemptiness hypothesis |

The affine regular hypotheses in both virtual-dimension statements are the ones on `f`
in the preceding sentence of the node. Intermediate smooth schemes are arbitrary
Noetherian schemes; they are not required affine or equipped with extra regularity.
The conormal rank is measured over the quotient of the ambient local ring by its stalk
kernel, canonically isomorphic to the source local ring for a closed immersion.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-sbc-affine-space`: `Mathlib/AlgebraicGeometry/AffineSpace.lean`, `AlgebraicGeometry.AffineSpace`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`.
- `def-per-regular-closed-immersion-codimension`: `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`, `AlgebraicGeometry.IsRegularClosedImmersionWithCodimension`.

Proof-dependency modules are imported without `public`; direct statement imports are
public. The imports include the regular-local quotient/parameter statements, principal
neighbourhood regularity, smooth-pair regular equations, conormal freeness, smooth conormal
exactness, flat tensor exactness, quotient base change, local dimension finiteness,
flat height and finite-type fibre dimension formulas, finite-spectrum maximality,
isolated-fibre residue finiteness, smooth fibre criterion, smooth relative-dimension local
constancy, and affine-space smoothness. No import cycle was encountered.

Searches:

- `msearch.py leanfinder`: regular closed immersion flat base change composition codimension
  smooth section intrinsic virtual dimension — eight hits on separate smoothness notions
  and stability properties, no whole-calculus statement.
- `msearch.py loogle`: `IsRegularImmersion, IsRegularClosedImmersion,
  SmoothOfRelativeDimension` — zero hits; unknown identifier `IsRegularImmersion`.
- `msearch.py grep`: `RegularImmersion|RegularClosedImmersion|regular immersion|virtualDimension`
  in Mathlib AlgebraicGeometry — zero hits.
- `msearch.py leansearch`: closed immersion locally generated by regular sequence with
  locally varying codimension — eight ordinary closed-immersion/immersion hits.
- `msearch.py leanfinder`: regular closed immersion with variable codimension local regular
  equations — eight ordinary immersion/smooth-dimension hits.
- Local `rg` on Mathlib, upstream WeilConjectures and side Sheaf, plus node searches and
  `tools/blueprint_refs.py search 'regular closed immersion'`, found only the fixed-pure-
  codimension upstream class and the specialized field/purity definition. The exact new
  predicate name and varying/variable-codimension searches had no matches.
- `rg` of the item id in upstream WeilConjectures had no matches. The upstream name index
  was consulted (`tools/lean_names_upstream.py show` and exact-name `rg`).

Edge cases checked against the definitions and formulas:

1. Identity: empty equations generate zero; c=0 and r=0 give virtual dimension zero.
2. Proper open-and-closed inclusion: along the included component its zero ideal has the
   empty sequence; no impossible empty-generator condition is imposed off the image.
3. Empty source into a nonempty scheme: regularity reduces to closedness, and the function
   from the empty source, rank assertion, formula and uniqueness are vacuous. An empty
   scheme is permitted to be affine; the presentation by a quotient of a polynomial ring
   onto the zero ring is included.
4. Section of A^r over a field: the conormal rank is r, and the relative composite is the
   identity, hence r-c=0. For r=0 the same argument has no equations.
5. A^1 over k at its generic point: local dimension is zero and residue trdeg is one;
   at a closed point they are one and zero. Both give r=1 for c=0.
6. Spec F_p → Spec Z: c=1 and r=0 give -1, so the formula must use integer subtraction.
7. Disconnected examples with different regular codimensions on the components: the
   function `c : Y → ℕ` allows them and local constancy asserts precisely the right result.
8. Flat base change with empty preimage: the base-changed codimension function is empty;
   no faithful flatness or nonempty-fibre condition is added.

No STATEMENT-DISPUTED issue or statement correction was needed. The original DAG statement
is retained verbatim. Both files compiled cleanly with the prescribed scompile wrapper;
only the expected postponed theorem proofs are present.

## New nodes

`def-per-regular-closed-immersion-codimension` supplies the general sourcewise nonnegative
codimension notion, from Stacks divisors.tex Tags 063D, 063G and 063J. Its one definition
is genuine Prop data, using Mathlib closed immersions, section-map kernels and regular
sequences. Local constancy and rank uniqueness are conclusions of the owning calculus
node, so the definition contains no postponed proof. The existing upstream pure-c class
imposes equations even off the source; in codimension zero that forces a zero ideal on
an ambient component disjoint from the source, excluding a proper clopen inclusion. The
landed def-pur-regular-immersion instead requires positive c and finite-type separated
schemes over a field. Neither gives this node's arbitrary Noetherian, varying-c notion.
The new node records the search outputs, and is added to the item's stmt_deps.

## Second reading by Q63

The dispatched worker reread the original JSON, both final modules, and the Stacks
regular-ideal/regular-immersion definitions. This is a worker self-check; the independent
maintainer review requested by the dispatcher is pending. No other agent was started.
The rereading verified all rows in the clause table, the order of pullback projections,
the term `d (i z)` in composition, the use of canonical residue maps, and integer rather
than natural subtraction. It corrected the `FiniteDimensional` explicit instance to the
module underlying the residue algebra and corrected the definition's source tags to
063D/063G/063J. No natural statement or proof was changed. The empty-source and proper
clopen codimension-zero examples specifically explain why the existing pure-c interfaces
cannot be reused unchanged.
