## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField` states
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_prescribed_residueField`, with
one `sorry` proof. No definitions are introduced, and the node changes only in `lean`.

The source is Stacks Project, More on Morphisms, Lemma 02LF:
https://stacks.math.columbia.edu/tag/02LF . The local Stacks checkout is absent on this
machine, so I opened this source online. Its statement is precisely the node's claim;
its proof reduces to the affine case and Algebra Lemma 00UD. The declaration docstring
records all five steps of the DAG proof, including residue-field compatibility.

Hypotheses and conclusion, clause by clause:

- A scheme S and a point s: `(S : Scheme.{u}) (s : S)`.
- A field extension k/κ(s): `(k : Type v) [Field k] [Algebra (S.residueField s) k]`.
  The extension map is `algebraMap (S.residueField s) k`.
- Finiteness of the field extension: `[FiniteDimensional (S.residueField s) k]`.
- Separable algebraicity: `[Algebra.IsSeparable (S.residueField s) k]`. This definition
  requires every minimal polynomial to be separable, which already implies algebraicity;
  an additional algebraicity hypothesis is unnecessary.
- A scheme U and a scheme morphism φ: `∃ (U : Scheme.{u}) (φ : U ⟶ S)`.
- The morphism is étale: `Etale φ` in the conjunction.
- A point u mapping to s: `∃ (u : U) (h : φ u = s)`.
- A field isomorphism k → κ(u): `(e : k ≃+* U.residueField u)`. A ring equivalence between
  fields is a field isomorphism.
- The isomorphism respects κ(s), embedded in κ(u) by φ: the equality for every
  `a : S.residueField s` says
  `e (algebraMap (S.residueField s) k a) =
  (φ.residueFieldMap u).hom ((S.residueFieldCongr h).inv.hom a)`.
  Mathlib's map has domain κ(φ(u)); the inverse of the equality-induced isomorphism
  transports a from κ(s) to that domain. Thus this is exactly compatibility with the
  induced residue-field map, not merely an abstract isomorphism of fields.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (available through the imports).
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`,
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, in
  `Mathlib.AlgebraicGeometry.ResidueField`. The same module's `residueFieldCongr`
  supplies equality transport, with no new notion or private definition.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.

Every dependency is a Mathlib leaf with `mathlib_match` rather than `lean`, as allowed.
Their full signatures and docstrings were read in the source checkout. Finiteness uses
`FiniteDimensional`, the standard abbreviation of `Module.Finite` read in
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`.

Edge cases checked before writing: an empty S has no s, so is vacuous; no assumption of
nonemptiness of S is added. The degree-one extension is realized by the identity
neighbourhood, including arbitrary presentations of the base field. All characteristics
are allowed; inseparable extensions are excluded exactly by the given hypothesis.
Neither s nor u is required to be closed. S need not be affine, Noetherian or separated,
and φ need not be finite or surjective. Universes u and v are explicitly bound and
independent: k may be a larger-universe presentation of its finite extension. U may be
chosen in S's universe because the affine construction uses a finite-presentation
R-algebra. Equality transport is in the correct direction κ(s) → κ(φ(u)).

Searches for an existing statement:

- `msearch.py ... leanfinder`: query "there exists an etale neighbourhood realizing a
  finite separable extension of the residue field of a scheme point". Eight results:
  polynomial universal factorization with bijective residue-field map, separability of
  residue fields for unramified local rings, étale loci, the canonical residue-field
  preimmersion, étale algebras over fields, and étale localization. None is this statement.
- `msearch.py ... loogle`: query
  `AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.residueField`. One result:
  `AlgebraicGeometry.Scheme.instEtaleFiberToSpecResidueField`, a base-change property,
  not prescribed residue-field realization.
- `msearch.py ... grep`: query
  `02LF|00UD|prescribed.*residue|residue.*prescribed`. No Mathlib hits.
- `rg -n 'prescribed|02LF|etale.*residue|residue.*etale'` over the source project's
  `WeilConjectures` and this project's `lean/Sheaf`: related slicing and residue-field
  separability statements, and the upstream affine theorem
  `Algebra.exists_etale_residueField_equiv` in
  `WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`. I read that theorem's full
  signature and docstring: it concerns a ring A and a prime ideal p, not a general
  scheme S and its point s, so does not already state this node.
- `rg -n 'exists_etale.*residueField|exists.*residueField.*equiv'` in upstream
  AlgebraicGeometry and Mathlib/AlgebraicGeometry: slicing results only, not this statement.
- `grep -rn` for the node id in upstream `WeilConjectures`: no hits.
- `rg -n 'exists_etale_neighbourhood_prescribed_residueField'` in
  `dag/lean_names_upstream.json`, upstream `WeilConjectures`, and `lean/Sheaf`: no hits;
  the chosen declaration name is new.

Server validation: `scompile.py E1 lem-weil-pbc-etale-neighbourhood-prescribed-residue-field`
with the module path compiled successfully (exit 0, 1.7 seconds), with no warnings.
No statement dispute, missing notion, unusable dependency, or node fault was found.

## Second reading by E1

I independently opened the node, the delivered Lean module, every statement dependency
node, and the corresponding Mathlib declarations. I read the Stacks TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
labels `section-etale-neighbourhoods`, `definition-etale-neighbourhood`, and
`lemma-realize-prescribed-residue-field-extension-etale` (current lines 9251–9312),
and checked the tag at https://stacks.math.columbia.edu/tag/02LF. The section imposes
no standing finiteness, separation, base-field or Noetherian hypothesis. Its preceding
definition of an étale neighbourhood requires exactly an étale morphism and a point
mapping to the given point; it does not require equal residue fields. The latter is
only the additional condition on an *elementary* neighbourhood.

Independent checklist of the node, with the Lean rendering and verdict:

- Object S, an arbitrary scheme: `(S : Scheme.{u})`. Exact. Mathlib `Scheme` is a
  locally ringed space locally isomorphic to affine spectra, and `Scheme.Hom` is a
  locally ringed-space morphism, as required by `def-pc-scheme`.
- Object s, a point of S: `(s : S)`. Exact; the scheme coercion is its underlying space.
- Object k, a field extension of κ(s): `(k : Type v) [Field k]
  [Algebra (S.residueField s) k]`. Exact. `Algebra.algebraMap` gives the specified
  embedding, and any field embedding induces this algebra structure. The dependency
  `def-pc-field-extension` records precisely `Algebra`, not a different notion.
- Hypothesis k/κ(s) finite: `[FiniteDimensional (S.residueField s) k]`. Exact;
  `FiniteDimensional` is `Module.Finite`, i.e. finite dimension over the field.
- Hypothesis k/κ(s) separable algebraic:
  `[Algebra.IsSeparable (S.residueField s) k]`. Exact. I read the protected class and
  `Algebra.IsSeparable.isAlgebraic`; separability of every minimal polynomial includes
  algebraicity, because a nonintegral element has minimal polynomial zero, which is
  not separable. No further algebraicity instance is required from the caller.
- Conclusion U, a scheme, and φ : U → S:
  `∃ (U : Scheme.{u}) (φ : U ⟶ S)`. Exact, with the existential objects following all
  universally given data.
- Conclusion φ étale: `Etale φ`. Exact. I read Mathlib's affine-local class and
  `Etale.iff_flat_and_formallyUnramified`, agreeing with the dependency's geometric
  description; no assumption of finiteness or surjectivity is introduced.
- Conclusion a point u with φ(u) = s: `∃ (u : U) (h : φ u = s)`. Exact.
- Conclusion a field isomorphism k → κ(u): `(e : k ≃+* U.residueField u)` under the
  existential. Exact: a ring equivalence between these fields is a field isomorphism.
- Conclusion that isomorphism is over κ(s): for every `a : S.residueField s`,
  `e (algebraMap (S.residueField s) k a) =
  (φ.residueFieldMap u).hom ((S.residueFieldCongr h).inv.hom a)`. Exact.
  I read `Scheme.residueField` as the stalk modulo its maximal ideal,
  `Hom.residueFieldMap` as the map induced by `f.stalkMap`, and `residueFieldCongr`
  as `eqToIso` on equal points. For h : φ(u) = s, the congruence inverse has source
  κ(s) and target κ(φ(u)), followed by φ's canonical map to κ(u). This equality is
  precisely compatibility of the two embeddings, not just an abstract field equivalence.

All five dependencies are usable Mathlib leaves; no private notion, new definition
node or dependency module is needed. There is no `statement_change`, and no source
or node correction is warranted.

Edge cases: an empty scheme has no s, so the assertion is vacuous. The degree-one
extension admits the identity neighbourhood and the given base-field embedding as
the field identification. Degree zero cannot occur for a field extension; this is
inherent in the objects, not an added hypothesis. Zero rings can occur in affine
charts only without points. Arbitrary characteristic and nonclosed points are allowed;
no global field or characteristic restriction occurs. Inseparable extensions are
excluded precisely by the node's separability hypothesis. No index set or integer n
is part of the statement. Universes u and v are bound independently. A finite extension
in Type v has an equivalent small presentation, and the standard étale construction
from finitely many polynomial coefficients over an affine chart in Type u yields U
in Scheme.{u}; thus the existential universe does not exclude large presentations of k.
The upstream affine theorem also explicitly uses independent universes with its
constructed algebra in the base ring's universe.

Independent searches, using other wording than the worker:

- `msearch.py ... leanfinder`: "Any finite separable extension of a scheme point
  residue field is realized as the residue field of a point on an etale scheme over
  it". Eight hits; universal polynomial factorization with *bijective* residue-field
  map, unramified local-ring residue fields, and canonical residue-field maps and
  spectra. None states the required existence for a general scheme and a prescribed
  finite separable extension.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme.Hom.residueFieldMap,
  AlgebraicGeometry.Etale`. Zero hits.
- `msearch.py ... grep`: `realiz.*residue|residue.*extension.*etale|02LF|00UD`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: "For a scheme S and point s every finite separable
  field extension of kappa(s) is isomorphic over kappa(s) to kappa(u) for an etale
  morphism U to S with u mapping to s". Service unavailable (Internal Server Error),
  recorded as unavailable; no mathematical verdict inferred from this failed service.
- Independent `rg -n -i 'realiz.*residue|residue.*realiz|neighbou?rhood.*separable|
  prescribed.*residue|02LF'` in upstream `WeilConjectures` and repository `lean/Sheaf`
  found the upstream ring theorem `Algebra.exists_etale_residueField_equiv`.
  I opened its full signature and docstring: the input is a commutative ring A, prime
  p, and extension of p.ResidueField; the output is an étale algebra A' and prime P
  with a compatible field equivalence. It is the affine algebraic ingredient, not
  this general scheme theorem, so it does not justify an `existing: true` delivery.
- `rg` for the delivered full name and node id in `dag/lean_names_upstream.json`
  and upstream `WeilConjectures` returned no hits. No name collision was found.

Mismatch and repair: none. I left the correct module and node record unchanged and
added this second-reading report. The declaration docstring includes the five proof
steps of the node: affine chart and residue identification, transport of the extension,
00UD, composition yielding the neighbourhood, and compatibility of the residue-field
isomorphism. Every proof dependency mentioned there is the corresponding DAG step.
There is exactly one theorem with `sorry`, no proved theorem and no data definition.
Header, namespace, imports, source annotations, explicit universes and variables are
correct; no line exceeds 100 characters. I checked programmatically that
`lean.statement` is verbatim the module signature before `:= by`.

Second-reader server compilation with `scompile.py` and the absolute sandbox module
path succeeded (exit 0, 1.8 seconds), with no errors or warnings. An initial invocation
using a relative path from the read-only repository could not locate the sandbox
module; it was corrected to the absolute path, without changing any source.
