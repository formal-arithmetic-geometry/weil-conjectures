## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeDivisorImageExtraction` states
`AlgebraicGeometry.exists_prime_divisor_image_extraction`, with `sorry` as its only proof.
It introduces no definitions or helper theorems. The node is unchanged except for `lean`.

Source read: Milne, *A Proof of the Barsotti-Chevalley Theorem on Algebraic Groups*,
arXiv:1311.6060v2, Lemma 4.4 and its proof, together with the terminology paragraph and
its use in the proof of Proposition 4.1:
https://arxiv.org/html/1311.6060v2#S4 . The node explicitly supplies the normal-source,
normal-model, supported-modification refinement of this source, with its seven-step proof.
The Lean docstring carries those seven steps and their named DAG prerequisites.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  `u` is explicit and arbitrary. All schemes are `Scheme.{u}`.
- The schemes V and P and the integral closed subscheme T are the binders `V P T` with
  `[IsIntegral V] [IsIntegral P] [IsIntegral T]`. In particular none is empty.
- Their k-structures are the actual morphisms `aV` and `aP` to `Spec (.of k)`.
  `[IsSeparated aV] [LocallyOfFiniteType aV] [QuasiCompact aV]` express that V is separated
  and of finite type. `[IsProper aP]` expresses properness of P and already implies
  separatedness and finite type. The implied structure on T is `i ≫ aV`; a closed immersion
  is finite, so T is separated and of finite type too. No additional condition on T is imposed.
- Normality of V and P is exactly `hV` and `hP`: every stalk is a domain and integrally closed.
  These are the node's explicit meaning of normal, not new definitions of a scheme property.
- The morphism f is dominant by `[IsDominant f]`, namely dense range. The equation
  `hf : f ≫ aP = aV` expresses that the morphism is over the base field, as required by the
  source's convention of working over k.
- T is a closed subscheme by `i : T ⟶ V` and `[IsClosedImmersion i]`. Its codimension is
  `hcodim : ringKrullDim (V.presheaf.stalk (i (genericPoint T))) = 1`.
  Mathlib's `genericPoint T` is the unique scheme generic point; its image under i has closure
  the support of the closed subscheme T. Thus the local ring used is that of V, not of T.
- The proper closed subset is `Z : TopologicalSpace.Closeds P` with `hZ : Z ≠ ⊤`.
  The inclusion f(T) in Z is `himage : Set.range (i ≫ f) ⊆ (Z : Set P)`.
- The conclusion provides `P' : Scheme.{u}` and `b : P' ⟶ P`.
  `IsIntegral P'` and the quantified normal-stalk condition give normal integrality.
  `IsProper (b ≫ aP)` makes P' proper over k (hence also separated and finite type).
  `IsProper b` is properness of the modification itself.
- `IsIso (b ∣_ Z.compl)` is precisely being an isomorphism over P minus Z. Mathlib's
  restriction has source the open inverse image and target this prescribed open.
- Birationality of this particular b is the witness `e : P'.PartialIso P` with
  `e.iso.hom ≫ e.target.ι = e.source.ι ≫ b`. The source and target of a Mathlib partial
  isomorphism are dense opens. The compatibility equation is necessary: abstract
  birationality of P' and P alone would not specify that b induces this isomorphism.
- `F : V.PartialMap P'` represents the rational lift. The equation
  `F.hom ≫ b = F.domain.ι ≫ f` specifies the actual lift of f over P. Because b is an
  isomorphism over the dense open P minus Z and f is dominant, this agrees there with
  b inverse composed with f and determines that rational map uniquely.
- `F.domain = F.toRationalMap.domain` requires F to represent the lift on its maximal domain,
  rather than on an unspecified smaller dense open. `i (genericPoint T) ∈ F.domain` is
  the asserted definition at eta_T. Such a maximal representative exists since the source
  is reduced and the target is separated; Mathlib supplies `RationalMap.toPartialMap`.
- `D : Scheme.{u}` and `j : D ⟶ P'` with `IsClosedImmersion j` and `IsIntegral D` give
  an integral, in particular reduced, closed subscheme. The equation
  `Set.range j = closure (F.hom '' {x | F.domain.ι x ∈ Set.range i})` identifies its support
  with the closure of the image of exactly T intersected with the full lift domain.
  This is a presentation of the reduced induced closed subscheme, unique up to unique
  isomorphism over P'; it does not permit an arbitrary thickening or arbitrary image.
- `Set.range j ⊆ b ⁻¹' (Z : Set P)` is the inclusion in the inverse image of Z.
- `topologicalKrullDim D + 1 = topologicalKrullDim P` expresses dim D = dim P minus one
  without truncated subtraction. These dimensions are finite because the schemes are
  of finite type over a field, and dim P is at least one under the hypotheses. Hence this
  is exactly the stated dimension equation, including the case dim P = 1.

Recorded statement dependencies used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (through the field imports).
- `def-weil-algebraic-closure`: `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`.
  The node's `mathlib_match.how` explicitly names `IsAlgClosed` for this clause; no chosen
  algebraic closure or algebraic extension is needed here.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` and `IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separated dependency.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`. The open subschemes and their immersions
  occur in the restriction, partial-map and partial-isomorphism interfaces.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`.

The recorded declarations and their source signatures/docstrings were read, including the
closed-scheme example's now-withdrawn Sheaf module and its actual upstream compact-object
module. All already stated proof dependencies have their modules imported without `public`
where they are not also statement dependencies. The proof-only
`lem-sfb-supported-valuation-finite-elements-model` currently has no Lean record; its import
is omitted until it is stated. It supplies no object needed to type this statement.
There are no new nodes, dependency repairs or statement corrections.

Edge cases checked before drafting:

- Empty V, P or T are excluded by the node's integrality, not an extra nonempty hypothesis.
- Z empty is allowed syntactically; since T is nonempty, the inclusion f(T) in Z is then
  impossible. Z equal to all of P is excluded exactly by the given strict inclusion.
- If dim P = 0, an integral finite type k-scheme has no nonempty proper closed subset;
  this is incompatible with the required image inclusion. The dimension equation therefore
  does not suppress a legitimate zero-dimensional case.
- For dim P = 1, the construction chooses an empty residue-independent family and D is
  zero-dimensional. The Lean statement has no positivity or nonempty-list assumptions.
- No restriction on characteristic is added. No assumption that f is proper, generically
  finite, surjective or birational is added. T is not assumed normal or Cartier.
- P' and D inherit separatedness and finite type from the stated properness and closed
  immersion; no projectivity or smoothness is required.
- The ring dimension is measured in the ambient stalk at the image of eta_T. The final
  dimension is topological dimension of D, not dimension of a local ring or a chosen chart.

Searches actually run:

1. `msearch.py ... leanfinder`: "A prime divisor under a dominant morphism has divisorial
   image after a proper birational modification of the target unchanged away from the image".
   Eight hits: normalization dominance, dominant composition/extensionality and rational-map
   representatives/function-field interfaces. None extracts a divisor by a supported modification.
2. `msearch.py ... loogle`: `"Scheme", "birational", "divisor"` returned zero hits.
3. `msearch.py ... grep`: `divisorial|divisor.*birational|birational.*divisor` returned zero hits.
4. `msearch.py ... leansearch`: "A proper birational modification makes the image of a prime
   divisor a divisor and is unchanged outside a prescribed closed subset". Eight hits:
   restriction of function-field maps, properness and integral morphisms; no exact statement.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `lem-sfb-prime-divisor-image-extraction|divisorial|divisor.*birational|birational.*divisor`
   and then `prime.divisor|prime_divisor|PrimeDivisor|image.extraction` found other divisor
   and log-geometry results, but no extraction theorem.
6. Source inspection in Mathlib found the existing `Scheme.PartialMap`, `Scheme.RationalMap`,
   `RationalMap.domain` and `Scheme.PartialIso` interfaces under
   `Mathlib.AlgebraicGeometry.Birational`, and the existing reduced induced subscheme
   construction `Scheme.IdealSheafData.vanishingIdeal`/`subscheme`.
   These confirm that all notions are already available; the theorem is new.

Validation: the prescribed `scompile.py` compiled this module in both sandbox and library
mode cleanly (1.8 s and 1.9 s on the initial version). Final compile and delivery preflight
results are recorded below.

## Second reading by Q04

Worker's second pass with the node and Lean module open, rather than an independent agent
review (the dispatcher explicitly prohibits starting other agents):

The normal stalk conditions agree for V, P and P'. The local codimension hypothesis uses
`i (genericPoint T)` in V. The base structure equation for f carries the source's k-map
convention. Properness of P and of P' uses their actual structure morphisms. Birationality
includes the compatibility equation with b, and the isomorphism restriction is over exactly
`Z.compl`. The image closure uses the maximal rational-map domain, includes eta_T there,
and takes T's support via the closed immersion i. Integral D implies reduced D, so the
closed immersion with this support specifies the reduced closure. The final equation
`dim D + 1 = dim P` is equivalent to the node's finite dimension equation. No mathematical
mismatch was found, no node correction is needed, and no assumptions were added to handle
an interface limitation. Explicit public imports of finite type, quasi-compactness and
open immersion were added in this pass to match the recorded statement dependencies.
The maintainer performs the independent delivery review specified by the brief.

Final validation: `deliver2.py Q04 lem-sfb-prime-divisor-image-extraction --no-push`
reported `OK (dry run): commit c7f9001d01a passes the preflight and compiles; nothing pushed`.
The node delta was checked to contain only `lean`, whose signature matches the source
verbatim. The module has one theorem, a sorry-only proof, and maximum line width 89.
