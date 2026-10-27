## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting` states
`AlgebraicGeometry.AlgebraicSpace.representable_etale_fppf_local_lifting` with a
single postponed proof. It introduces no definitions and does not change the node's
statement, statement dependencies, proof, or proof dependencies.

Hypotheses and clauses, read against the node:

- `S : Scheme.{u}` is the base scheme. `Over S` objects are schemes with their
  structure maps to S, and morphisms in `Over S` are S-morphisms.
- `F : Sheaf (Scheme.fppfTopology.over S) (Type u)` is an arbitrary sheaf of sets on
  the big fppf slice site. No `AlgebraicSpace S` or representable diagonal is assumed.
- `U : Over S` is the source scheme. The source of `p` is
  `(Scheme.fppfTopology.over S).yoneda.obj U`, whose underlying presheaf is precisely
  `yoneda.obj U`, taking T to `T ⟶ U`. Thus `p` is exactly the node's sheaf map.
- `hp : IsEtale p.hom` and `hs : IsSurjective p.hom` are the dependency's scheme-test
  predicates, including representability. They require the respective property on a
  scheme representing each pullback; uniqueness of a representing square gives the
  two properties on the same projection. No extra representability assumption is needed.
- The first conclusion quantifies over every `T : Over S` and every
  `ξ : F.obj.obj (op T)`. It supplies `V : Over S`, `v : V ⟶ T`, and `a : V ⟶ U`.
- `IsPullback (yoneda.map a) (yoneda.map v) p.hom (yonedaEquiv.symm ξ)` is the
  representing pullback square, with the two named projections. Here
  `yonedaEquiv.symm ξ` evaluates at b as F(b)(ξ). This square in presheaves also
  represents the sheaf pullback, since all four objects are sheaves and their limits
  are computed in presheaves. This states representability with the actual projections,
  rather than just an abstract isomorphism to an unspecified pullback.
- `p.hom.app (op V) a = F.obj.map v.op ξ` is exactly the local lift equality.
- `Etale v.left ∧ Surjective v.left` asserts both properties for the underlying
  scheme map V → T.
- `Sieve.generate (Presieve.singleton v) ∈ (Scheme.fppfTopology.over S) T` says the
  singleton is a covering family on this slice site. Together with the displayed
  surjective étale property it is the node's actual fppf covering, not an arbitrary
  covering obtained without control of its member.
- `Sheaf.IsLocallySurjective p` is the covering-image-sieve form of local
  surjectivity. The preceding singleton witnesses it for every section.
- `Epi p` is an epimorphism in the category of fppf sheaves of sets, not a
  presheaf epimorphism or sectionwise surjectivity assertion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies
  `GrothendieckTopology.over` (def-pc-fppf-site). The generated singleton sieve is
  expressed with Mathlib's `Presieve.singleton` and `Sieve.generate`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace.IsEtale`,
  `AlgebraicSpace.IsSurjective`, and their underlying `IsRepresentableWith`
  definition (def-trf-algebraic-space). The full node module and docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (def-weil-etale-morphism).
- `Mathlib.CategoryTheory.Sites.LocallySurjective`: `Sheaf.IsLocallySurjective`,
  `Sheaf.isLocallySurjective_iff_epi`, and `Sheaf.epi_of_isLocallySurjective'`
  (proof dependency lem-weil-pbc-site-sheaf-sets-epi-locally-surjective). This import
  is public because the local-surjectivity predicate occurs in the statement.
- `Mathlib.CategoryTheory.Sites.SubcanonicalOver` provides the slice-site
  subcanonical instance, and `Mathlib.CategoryTheory.Sites.Subcanonical` provides
  the existing sheaf Yoneda API. No new sheaf of morphisms is defined.

Source read: Stacks `spaces.tex`, `lemma-space-presentation` (0262), proof of (3),
which forms V = T ×_F U and obtains a local lift on its singleton fppf cover;
`topologies.tex`, `definition-fppf-covering` (021M), and `sites.tex`,
`definition-sheaves-injective-surjective` (00WM) and `lemma-mono-epi-sheaves` (00WN).
The paragraph uses only scheme-test representability and surjective étaleness,
as the item explicitly says; the ambient algebraic-space diagonal is not used.

Edge cases checked before writing: empty T and empty V are allowed, with no
nonemptiness binder. A surjective map from empty U forces its test schemes to be
empty as appropriate; no global section lift is claimed. A non-quasi-compact
surjective étale map is allowed because only local finite presentation is needed.
The test schemes and F-values use the dependency's universe u: `Over Scheme.{u}`
has morphisms in Type u; no smaller independent test universe or equality of site
object and morphism universes is imposed. Arbitrary characteristic is allowed.
Identity maps fit the same statement. No separate algebraic-space assumption or
representable-diagonal hypothesis enters any clause.

Searches performed (the wrapper records are in sandbox `searches.jsonl`):

- msearch LeanFinder: "A representable surjective etale map from a scheme to an
  fppf sheaf has local lifts on the singleton fppf covering given by its scheme
  pullback and is an epimorphism". Eight results included the general sheaf
  epi/local-surjectivity equivalence, scheme covers, and a Zariski gluing result;
  none states the complete scheme-test pullback/local-lifting conclusion.
- msearch LeanFinder: "representable surjective etale sheaf map fppf local lifting".
  Eight results, again general representability and local-surjectivity results,
  not the complete item.
- msearch Loogle: `"IsLocallySurjective", "Etale"`: zero results.
- msearch grep: `IsRepresentableWith|etale.*isLocallySurjective|isLocallySurjective.*etale`:
  zero results in Mathlib.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for
  representability, étale local lifts, `IsRepresentableWith`, and fppf/epi phrases;
  direct grep for the item id in `lean/WeilConjectures`; no existing declaration
  states the complete item. Read the nearby representable-étale scheme tests,
  fppf covering calculus and atlas presentation modules: those concern algebraic
  spaces, do not provide this explicit conclusion for arbitrary F, or merely cite
  this local-lifting argument in their proof documentation.
- Checked the proposed declaration name in the project and upstream-name index;
  no name collision found.

Validation: scompile.py compiled the module in both sandbox and library module
modes on the server, cleanly (1.9 s and 1.8 s). All variables and the universe are
explicitly bound; `set_option autoImplicit false` is set. The only proof is `sorry`.
No node faults or STATEMENT-DISPUTED issues were found.

## Second reading by Q29

The dispatcher requires this worker to deliver without spawning another agent;
the maintainer supplies the independent review. A separate self-reading of the node
and final Lean checked the clause mapping above. In particular, the target is F as
an arbitrary sheaf, the pullback is along the section's actual Yoneda map, the lift
has the correct contravariant restriction `F.obj.map v.op ξ`, the same v has both
scheme properties and generates the singleton covering, and the epi is a sheaf epi.
The sheaf Yoneda source is definitionally the dependency's presheaf Yoneda source.
No extra diagonal, quasi-compactness, nonemptiness, or global-lift condition was
introduced. No mismatch required a statement change or a dependency repair.
