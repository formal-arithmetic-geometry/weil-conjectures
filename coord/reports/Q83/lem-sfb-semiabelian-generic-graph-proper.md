## Worker report

Item: lem-sfb-semiabelian-generic-graph-proper. The module
`Sheaf.AlgebraicGeometry.SemiabelianGenericGraphProper` states
`AlgebraicGeometry.semiabelian_generic_graph_proper`, with exactly one `sorry`.
It also constructs `AlgebraicGeometry.semiabelianFibreGraphMap` by `pullback.lift`.
This helper belongs to the graph construction of the item, is listed in
`lean.declarations`, and has genuine data: its compatibility proof is a composition
of `Scheme.Hom.fiber_fac`, `Over.w` and associativity equalities. It introduces no
new mathematical notion or postponed lemma.

The source is Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1 proof, printed pages 10-11. I opened the primary PDF
https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf
and checked the paragraph forming the closure of the graph and asserting the first
projection proper after valuation-ring base changes. The accepted node isolates
that properness assertion. The node statement, statement dependencies and proof
are unchanged. There is no disputed statement or dependency repair.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| S is a scheme | `{S : Scheme.{u}}`, with explicit `universe u` and `autoImplicit false` |
| S integral | `[IsIntegral S]`, including nonemptiness |
| S locally Noetherian | `[IsLocallyNoetherian S]` |
| Every local ring is an integrally closed domain | `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| P,Q are group schemes over S | `(P Q : Grp (Over S))`; the underlying structure morphisms are `P.X.hom`, `Q.X.hom` |
| Commutativity | `[IsCommMonObj P.X] [IsCommMonObj Q.X]` |
| Multiplication, identity and inverse are morphisms satisfying group identities | The existing bundled `Grp (Over S)` structure, with no pointwise replacement |
| Smooth P,Q | `[Smooth P.X.hom] [Smooth Q.X.hom]` |
| Separated, diagonal a closed immersion | `[IsSeparated P.X.hom] [IsSeparated Q.X.hom]`; this is Mathlib's diagonal definition |
| Finite presentation | `[LocallyOfFinitePresentation P.X.hom] [QuasiCompact P.X.hom]` and the same for Q; separatedness supplies quasi-separatedness |
| Semiabelian geometric fibres | `hP : HasSemiabelianGeometricFibres P`, `hQ : HasSemiabelianGeometricFibres Q` |
| eta the generic point | `genericPoint S` |
| K its residue field | `S.residueField (genericPoint S)`, the target spectrum of `S.fromSpecResidueField (genericPoint S)` |
| Actual generic scheme fibres with their induced group laws | `(Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj P` and similarly Q; the underlying schemes are definitionally `P.X.hom.fiber (genericPoint S)` and Q's fibre |
| u a K-group homomorphism | The displayed binder `u` is a morphism in `Grp (Over (Spec (S.residueField (genericPoint S))))` |
| Generic graph map followed by the map to P times_S Q | `semiabelianFibreGraphMap P Q (genericPoint S) u`, using components `P.X.hom.fiberι` and `u.hom.hom.left ≫ Q.X.hom.fiberι` |
| Gamma the scheme-theoretic image, with its scheme structure | `(semiabelianFibreGraphMap P Q (genericPoint S) u).image`, Mathlib's kernel-ideal subscheme |
| pi first projection from Gamma | `(semiabelianFibreGraphMap P Q (genericPoint S) u).imageι ≫ pullback.fst P.X.hom Q.X.hom` |
| pi is proper | `IsProper` of precisely that composite |

Dependency declarations used, after opening their full source signatures and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsDomain` and `IsIntegrallyClosed`, inline for each local ring as the node requires.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; `QuasiCompact` and `IsSeparated` supply
  the global finite-presentation conditions.
- `def-sfb-semiabelian-geometric-fibres`: `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`,
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`, with its given kernel square and fppf
  local-surjectivity condition for every geometric fibre.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.lift` (available through the imports).
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, `fiber_fac`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.fromSpecResidueField`, available through Fiber.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; separatedness uses this on the diagonal and
  the image inclusion has this property canonically.
- `def-nagata-scheme-theoretic-image`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `AlgebraicGeometry.Scheme.Hom.image`, `imageι` (both use `Hom.ker`).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` and `IsSeparated`.

All stated proof dependencies are imported privately unless their module already
supplies statement definitions publicly. These include the geometric-power integrality,
algebraic-closure connectedness test, upstream smooth-connected generic geometry core,
reduced scheme image, upstream scheme-image flat base change and valuation closed
factorization, trait extension, and generic-DVR properness criterion modules. The generic
Noetherian, finite-type, smooth/proper base-change and closed-immersion dependencies use
Mathlib's existing interfaces; their modules are already among the imports. No downstream
normal-semiabelian extension theorem is imported or used to replace the accepted proof.
The seven-step proof plan is included in the theorem's docstring.

Edge cases checked before writing:

- The empty base is excluded by the node's integrality assumption, not by an extra binder.
- Trivial group schemes and rank-zero torus parts are permitted by the recorded predicate;
  their graph projections are isomorphisms, so properness has the correct interpretation.
- Pure tori are permitted. For G_m over an integral normal base, integer-power generic
  homomorphisms (including exponent zero and negative exponents) have graphs with
  isomorphic first projection. There is no improper extra assumption that Q itself is proper.
- Abelian schemes and mixed torus/abelian fibres remain permitted without a fixed torus rank.
- All residue characteristics and nonexcellent, non-quasi-compact locally Noetherian
  bases are retained; no completeness, characteristic, excellence or base qc assumption appears.
- The base-change functor preserves the actual group laws; an arbitrary scheme map does
  not masquerade as the generic homomorphism. The helper also works at nongeneric points,
  but the theorem uses exactly the unique generic point of the integral base.
- The image is the full scheme-theoretic image, not its topological range or a reduced
  substitute, and the conclusion has no hypothesis assuming the projection proper.
- The explicit universe u matches schemes, residue fields and the existing geometric-fibre
  predicate; no extra universe equality is imposed.

Searches performed on 2026-10-24:

1. `msearch.py ... leanfinder "The schematic closure of the graph of a generic homomorphism
   of semiabelian schemes has proper first projection"`: eight general properness hits,
   including `Scheme.Hom.isProperMap`, `IsProper.instFstScheme`, `UniversallyClosed`.
   None establishes the item; the projection instance assumes Q proper, which the item does not.
2. `msearch.py ... loogle '"IsProper", "image"'`: three hits about topological proper maps
   and compact preimages, no semiabelian graph closure statement.
3. `msearch.py ... grep 'semi.?abelian|graph.*closure|closure.*graph' AlgebraicGeometry`:
   zero Mathlib hits.
4. `msearch.py ... leansearch "The graph closure projection of a generic homomorphism of
   semiabelian schemes over a normal integral base is proper"`: eight properness/finite-map
   interface hits, no exact statement.
5. `rg -n 'semi.?abelian|generic.*graph|graph.*proper' lean/WeilConjectures lean/Sheaf`:
   found the existing trait and normal extension interfaces and unrelated proper graph
   results; none states this item. The normal extension module mentions this node in its
   proof plan, so it must not become the proof input for this node.
6. `grep -rn 'lem-sfb-semiabelian-generic-graph-proper' lean/WeilConjectures`: no hits.
7. `rg -n 'semiabelianFibreGraphMap|semiabelian_generic_graph_proper'` across Mathlib,
   `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing
   declaration with either proposed name. Existing graph-image results in upstream
   Pullbacks require a proper second factor and concern partial sections on opens.

Validation: prescribed `scompile.py Q83 lem-sfb-semiabelian-generic-graph-proper
<module path>` passed both sandbox and library-name compiles, 2.7 seconds each, with
no errors or warnings. The node JSON changes only `lean`; its signature is copied verbatim
from the theorem in the file. Every source line is at most 100 characters.

## Second reading by Q83

Single-worker self-audit (no separate agent was started; the dispatcher explicitly
forbids that). The maintainer supplies the independent review. I reopened the node and
module and compared each clause using the table above. In particular, finite presentation
includes qc and the quasi-separatedness supplied by separatedness; the generic domain of
u is the same pullback as `fiber`; and the helper's two components define exactly (1,u)
followed by the map to the original product. Its equality proof only uses the fact that
u is over the residue-field spectrum. The final composite starts at the actual image
subscheme and lands in P. No statement mismatch, omitted hypothesis, additional conclusion,
private replacement definition, or hollow data construction was found. No correction or
new/dependency node is needed. The only postponed theorem is the item's own theorem.
