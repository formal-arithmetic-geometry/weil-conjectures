## Worker report

Item: lem-sfb-space-quasiaffine-affine-factorization. Group: Q38. Stage 2.

The new module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiAffineAffineFactorization`
states
`AlgebraicGeometry.AlgebraicSpace.exists_quasiCompact_openImmersion_affine_factorization`.
Its sole theorem has proof `by sorry`; no definitions or auxiliary theorems are introduced.
The docstring carries all six steps of the accepted DAG proof with the supporting node ids.
The mathematical statement is unchanged. The item gains two already-landed statement
dependencies for predicates it uses: `def-sfb-space-affine-quasifinite-properties` and
`def-sfb-space-quasi-compact-presheaf-map`. The etale-local theorem remains a
proof dependency only. No dependency record is repaired.

Clause-by-clause correspondence:

* The base scheme is `{S : Scheme.{u}}`; the two spaces over that same base are
  `{X Y : AlgebraicSpace S}`. Their map is `(f : X ⟶ Y)`, a natural transformation
  in the full subcategory of fppf sheaves. `universe u` and `set_option autoImplicit false`
  make the size and variable bindings explicit; there is no extra universe equality.
* The representability clause in quasi-affineness is
  `hrep : IsRepresentable f.hom.hom`. This uses the dependency's full scheme-test
  predicate, including non-affine tests, rather than presuming scheme sources.
* For every affine scheme test the node requires a quasi-compact open subscheme
  of an affine scheme. `hqa` quantifies over `(T : Over S)`, `IsAffine T.left`, and
  every `a : yoneda.obj T ⟶ Y.obj.obj`. The witness `(U : Over S)` has
  `U.left.IsQuasiAffine`. Mathlib's existing scheme predicate includes compactness,
  and its canonical map `U.left.toSpecΓ` is an open immersion into an affine scheme.
  Conversely a quasi-compact open subscheme of an affine scheme is quasi-affine
  by `Scheme.IsQuasiAffine.of_isImmersion`. Thus no condition is lost or added.
  The scheme maps `p`, `q` and `IsPullback q (yoneda.map p) f.hom.hom a` identify
  this scheme as the actual pullback with its projection; a mere arbitrary
  quasi-affine scheme or an unnormalized arrow would not suffice.
* The envelope is `∃ (Z : AlgebraicSpace S)`, and the required maps are
  `(j : X ⟶ Z)` and `(p : Z ⟶ Y)`.
* Quasi-compactness of the open immersion is
  `IsQuasiCompactPresheafMap j.hom.hom`. This is the existing predicate that each
  affine test has a quasi-compact scheme atlas mapping surjectively and etale
  onto the pullback, exactly the node's atlas definition of quasi-compactness.
* Openness and representability are
  `IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) j.hom.hom`.
  This is exactly the predicate used by the recorded `OpenSubspace` definition,
  now applied to the morphism rather than imposing a literal chosen subfunctor.
  Every scheme test is represented by an open immersion, not just affine tests.
* The second map is affine by `MapIsAffine p`: its affine scheme tests are
  represented by affine schemes with specified pullback squares. Affine-local
  representability gives representability on all scheme tests, so this is the
  node's affine morphism notion. This is the shared predicate, with no copy.
* The equation `j ≫ p = f` is the node's `p ∘ j = f`, with category-theoretic
  composition notation in source-to-target order.
* The node's introductory definitions of quasi-separated spaces and morphisms
  are terminology, not assumptions on S, X, Y or f. Consequently no unused
  quasi-separatedness binder, quasi-compact-target hypothesis, finite-type
  hypothesis, or assertion about a chosen relative Spec is added.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentable`, and `AlgebraicSpace.IsRepresentableWith`.
  Read their definitions, including the scheme-valued pullback square.
* `def-weil-size-convention` is a convention record; explicit universes implement it.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; read their signatures and proof docstrings.
  Pullback squares in `hqa` are the representing presheaf form of these sheaf
  fibre products; no second fibre-product construction is introduced.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, whose
  scheme-test `IsRepresentableWith` predicate is used for j.
* `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap` (the exact compact-atlas predicate, owned by
  `def-sfb-space-quasi-compact-presheaf-map`, Q97 existing:true record) and
  `quasiCompact_separated_etaleLocal` (owned by
  `lem-trf-space-qc-separated-etale-local`, retained in `proof_deps` only).
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
* `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine`,
  `Scheme.IsQuasiAffine.of_isImmersion`, and its canonical-open-immersion instance.

Every recorded proof dependency with a module is imported. The additional Mathlib
proof imports supply the canonical quasi-affine embedding, affine qcqs and morphism
permanence, closed-immersion base change, and `ΓSpec.adjunction`. The module also imports
the affine-etale-cover, quasi-coherent-module, direct-image, relative-Spec, module-operations,
quasi-coherent-pullback, etale-pushforward-restriction and open-immersion-locality modules
recorded in `proof_deps`. Only statement interfaces are public imports; proof-only
interfaces are ordinary imports. No import was omitted for a cycle.

Source and edge cases:

Read the local Stacks `spaces-morphisms.tex`, Tag 086S
(`lemma-characterize-quasi-affine`) and Tag 081X
(`remark-factorization-quasi-compact-quasi-separated`). The former gives openness
of the canonical relative-Spec map; the latter constructs it from the evaluation
counit. The node's stronger input definition of quasi-affineness already implies
quasi-compactness and separatedness, as its accepted proof derives. No source-based
correction is needed.

Checked the empty source: the zero section algebra has empty relative spectrum and
provides the required factorization; no nonempty scheme or nontrivial-ring assumption
occurs. For empty Y, existence of f forces empty X, so the same case applies. For an
affine f, take Z = X and j the identity. For Y non-quasi-compact or non-quasi-separated,
the proof uses arbitrary affine etale charts and etale descent, never a finite cover
of Y. The conclusion imposes no absolute quasi-compactness on X or Z. All tests and
spaces use the fixed universe of S. No target-property assumptions exclude these cases.

Searches for existing statements and notions:

* `msearch.py ... leansearch "quasi-affine algebraic space morphism factorization open
  immersion affine morphism"`: 8 results, chiefly the canonical open immersion for
  quasi-affine schemes, open-immersion predicates and scheme quasi-affineness permanence;
  no algebraic-space affine-factorization statement.
* `msearch.py ... leanfinder "A quasi-affine morphism of algebraic spaces factors as a
  quasi-compact open immersion followed by an affine morphism"`: 8 results, including
  `Scheme.IsQuasiAffine.of_isAffineHom`, `Scheme.IsQuasiAffine.of_isImmersion`,
  `Scheme.IsQuasiAffine`, its canonical-open-immersion instance, and `IsAffineHom`;
  none states the desired algebraic-space factorization.
* `msearch.py ... loogle "AlgebraicGeometry.IsQuasiAffineHom,
  AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith"`: no hits; the former identifier
  is unknown to Loogle. Therefore no supposed Mathlib morphism API was assumed.
* `msearch.py ... grep "quasiAffine.*factor|quasi_affine.*factor|IsQuasiAffineHom|class
  IsQuasiAffine" AlgebraicGeometry`: one Mathlib result, the scheme class in
  `Mathlib/AlgebraicGeometry/QuasiAffine.lean:34`.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `quasiAffine.*factor|quasi_affine.*factor|quasiaffine.*factor|MapIsQuasiAffine`:
  no existing declaration of this statement or a separate space morphism predicate.
  Broader quasi-affine searches found the scheme descent modules and
  `SpaceQuasiAffineAffineDescent`, whose theorem is faithful-flat affine-base descent,
  not the present factorization. The upstream-name index has no matching space
  quasi-affine factorization declaration.
* Targeted `rg` on algebraic-space modules found `MapIsAffine` in
  `AlgebraicSpaceAffineQuasiFinite` and `IsQuasiCompactPresheafMap` in
  `SpaceQCSeparatedEtaleLocal`; both are reused and their owning nodes added to
  `stmt_deps`. The OpenSubspace node already supplies the open-immersion predicate.
* `python3 tools/blueprint_refs.py search 'quasi-affine'`: 13 blueprint-node results,
  primarily Nagata scheme notions; none is the present space-level factorization.
  No new notion is needed: the affine-test hypothesis uses Mathlib's existing
  quasi-affine scheme definition directly.

Validation: the prescribed `scompile.py Q38
lem-sfb-space-quasiaffine-affine-factorization <module>` completed successfully
on the live server: sandbox check 4.8 s, library check 1.7 s, no errors or warnings.
The prescribed deliver2.py --no-push dry run passed preflight and compilation
with commit 381f9c938dc (nothing pushed). The final delivery follows this check. No STATEMENT-DISPUTED claim,
statement change, new node, hollow definition, or dependency-module repair is present.


## Repair of returned delivery 0c9b6921bf00

H2: replaced `lem-trf-space-qc-separated-etale-local` in `stmt_deps` with
`def-sfb-space-quasi-compact-presheaf-map`. Read the existing Q97 definition-node
record and checked that it owns precisely
`AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap` in
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`. The statement uses this plain
definition; it does not need the etale-local theorem's conclusion. The theorem
remains in `proof_deps` for proof steps 1 and 6. The module, theorem signature,
proof docstring, source statement and accepted mathematical content are unchanged.

Compared the retained sandbox packet with current main: before this repair only
`lean` and the two added `stmt_deps` differed. The repaired packet retains that
field scope, now citing the correct definition owner. Delivery tooling builds the
repair on current main. No dependency file is edited or new node introduced.
The original delivery's reported compiler/dry-run checks above are historical;
the repaired packet is compiled and checked again before delivery.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
