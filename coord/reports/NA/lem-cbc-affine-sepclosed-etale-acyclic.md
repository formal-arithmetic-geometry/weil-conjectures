## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic` states
`AlgebraicGeometry.Scheme.subsingleton_H_of_affine_closed_isSepClosed`, with proof `sorry`.
The source was read at `literature/stacks-project/etale-cohomology.tex`,
`lemma-affine-only-closed-points` (Tag 09AY), including its proof.
No node correction, new notion, or dependency repair is needed.

Hypotheses and conclusion, clause by clause:

- The affine scheme is `(T : Scheme.{u}) [IsAffine T]`. Mathlib's `IsAffine`
  says the canonical morphism to Spec of global sections is an isomorphism.
- Every point is closed is exactly `hclosed : ∀ t : T, IsClosed ({t} : Set T)`.
- Every residue field is separably closed is
  `hsep : ∀ t : T, IsSepClosed (T.residueField t)`.
  Mathlib's residue field is the quotient of the structure-sheaf stalk by its maximal ideal.
- An arbitrary abelian sheaf on the small étale site is
  `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  This uses the project's standard large coefficient universe for a small étale site
  of schemes in universe u. There is no finite-generation, finiteness, or torsion restriction.
  The universe u is arbitrary; no finite or countable coefficient size is required.
- A positive integer degree is `(i : ℕ) (hi : 0 < i)`; positive integers and positive
  natural numbers have the same degrees. Degree zero is deliberately excluded.
- Vanishing is `Subsingleton (Sheaf.H F i)`. `Sheaf.H` is the existing cohomology
  of the whole site, Ext from the constant free rank-one abelian sheaf. It computes
  right derived global sections, and its degree-zero identification is
  `Sheaf.H.equiv₀` at the terminal étale object `Scheme.Etale.mk (𝟙 T)`.
  A subsingleton abelian group is the zero group. This is genuine global cohomology,
  without an arbitrary evaluation object or an assumed cohomology-vanishing map.
- No noetherianity, finite type, reducedness, or coefficient restriction was added.

Statement dependencies used (source signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`, via separable polynomials splitting.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; this recorded site convention retains
  Mathlib's `Sheaf` and cohomology definitions for the remaining components.
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `Sheaf.H` (and its
  degree-zero identification). Grothendieck sheaf and concrete-coefficient imports supply
  sheafification and Ext without assuming additional mathematical hypotheses.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  with its field instance (the node also records `Scheme.Hom.residueFieldMap`).

All recorded proof dependencies with available modules are imported, including the
profinite-spectrum theorem, minimal prime existence/localization, affine stalk/function
field results, dimension-zero strict henselianity, the Zariski/étale comparison, and
profinite topological cohomology vanishing. The declaration docstring records each of
four proof steps with the DAG ids. No theorem has been proved here.

Edge cases: the empty affine scheme is allowed (the two pointwise conditions are
vacuous and the sheaf cohomology still vanishes). Nonreduced schemes are not excluded;
zero-dimensional local rings may have nilpotents. Disconnected and infinite profinite
spectra are allowed. No characteristic restriction is present. The zero sheaf is allowed.
For a nonzero constant sheaf on a separably closed field, degree zero need not vanish,
which is why the strict inequality is necessary. An algebraically nonclosed separably
closed field in positive characteristic is still included.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`, query "Higher etale cohomology of abelian sheaves vanishes
  on affine schemes with all points closed and separably closed residue fields":
  eight hits, concerning formally étale algebras/cotangent complexes, the étale locus,
  and vanishing of structural sections in affine limits. No exact theorem.
- `msearch.py ... loogle`, query `"smallEtaleTopology", "Subsingleton"`: zero hits.
- `msearch.py ... grep`, query
  `etale.*acyclic|closed.*points.*cohomology|cohomology.*strictlyHenselian`: zero hits.
- `rg` over Mathlib/upstream/project sources: searched acyclicity and
  `affine.*sepclosed|sepclosed.*affine|subsingleton_H.*closed|lemma-affine-only-closed-points`.
  The affine closed injective theorem requires injective coefficients; the separably
  closed point theorem concerns a single spectrum of a field; neither is the present
  arbitrary-sheaf assertion for all affine zero-dimensional schemes.
  The downstream functions-quotient module cites this node but does not state it.
- `rg` for this node id in `WeilConjectures` and `dag/lean_names_upstream.json`:
  no recorded exact declaration. The new full declaration name has no existing match.

Validation: compilation and the delivery dry run are recorded after completion below.

`scompile.py` passed without errors or warnings, including both sandbox and library-path
compilation. `deliver2.py --no-push` printed OK: the commit compiles and passes preflight
except for the independent second reading, which is reserved for the second reader.
Nothing was pushed. Exact-name search also found no collision in Mathlib, upstream,
or the project's existing Lean modules.


## Second reading by NA

I independently read the base node, sandbox node and module, and Stacks
`etale-cohomology.tex`, Tag 09AY, `lemma-affine-only-closed-points`, with its
surrounding text and proof. This lemma is self-contained: no ambient
noetherianity, base field, characteristic, finite type or torsion assumption
is inherited. Its two numbered hypotheses and its conclusion agree with the
node. There is no statement_change, new node or dependency module in this delivery.

The object/hypothesis/conclusion checklist is:

1. An arbitrary scheme T: `(T : Scheme.{u})`. The recorded Scheme declaration
   extends LocallyRingedSpace with a local affine cover. Verdict: same object.
2. Affineness: `[IsAffine T]`. I opened Mathlib's class, which states that
   `T.toSpecΓ` is an isomorphism; this is precisely being a spectrum, with no
   reducedness assumption. Verdict: exact.
3. Every point is closed: `hclosed : ∀ t : T, IsClosed ({t} : Set T)`.
   Verdict: exact, not merely closed points having a property.
4. Every residue field is separably closed:
   `hsep : ∀ t : T, IsSepClosed (T.residueField t)`. I opened the recorded
   residue-field and IsSepClosed declarations: the former is the residue
   field of `T.presheaf.stalk t`, and the latter requires separable
   polynomials to split. These are the node's notions. Verdict: exact.
5. Every abelian sheaf on the small étale site:
   `(F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`. I opened the
   recorded smallEtaleTopology declaration: it is the topology induced by
   jointly surjective étale families on étale T-schemes. The coefficients
   use the established small-site u+1 size convention, with u arbitrary.
   The imported ConcreteCoefficients and GrothendieckAbelian.Sheaf instances
   supply sheafification, enough injectives and HasExt; none is an extra
   binder or mathematical assumption on T or F. Verdict: exact.
6. Every positive degree: `(i : ℕ) (hi : 0 < i)`. Positive integer degrees
   are exactly positive natural degrees. Verdict: exact.
7. Vanishing of right derived global sections:
   `Subsingleton (Sheaf.H F i)`. I opened SheafCohomology.Basic: H is Ext
   from the constant free rank-one abelian sheaf, whose Hom functor is global
   sections (its `H.equiv₀` evaluates at a terminal object). Thus these Ext
   groups are the right derived global sections, not evaluation at an
   arbitrary site object. Subsingleton means this abelian group is zero.
   The dependency SiteCoveringAxioms explicitly retains Mathlib cohomology.
   Verdict: exact, with no omitted conclusion or reordered dependency.

Edge cases: the empty affine scheme is admitted, with vacuous pointwise
conditions; the zero sheaf is admitted. There is no index-set binder to
restrict an empty family. Degree zero is correctly excluded (already a
separably closed field can have nonzero global sections). Nonreduced and
infinitely disconnected affine schemes are admitted. Every characteristic,
including imperfect separably closed fields, is admitted. No universe is
unbound and the size convention does not impose equality of independent
site object and morphism universes.

Independent H4 searches: `msearch.py ... loogle '"Sheaf.H", "IsAffine"'`
returned zero hits; LeanFinder on “Abelian sheaf on a zero dimensional affine
scheme with separably closed residue fields has vanishing higher cohomology”
returned eight hits about cotangent cohomology, trivial-group cohomology and
subsingleton affine schemes, none the present theorem. The grep service for
`zero.dimension.*etale|etale.*zero.dimension|isSepClosed.*Subsingleton`
returned zero hits. I also ran rg over Mathlib algebraic geometry, upstream
WeilConjectures algebraic geometry, project AlgebraicGeometry and Paper,
and the upstream-name inventory. Affine quasi-coherent cohomology,
injective sheaf vanishing, and curve/torsion vanishing do not assert this
arbitrary abelian étale-sheaf theorem. The exact new name and blueprint id
have no upstream collision. No replacement existing declaration was found.

H5/H6/H8/H9: there are no definitions or private copies, and the only
new theorem has proof `sorry`. Its module and declaration docstrings give
Tag 09AY and the blueprint id; its four proof steps faithfully retain the
node's profinite-spectrum, strictly-henselian-stalk, Zariski comparison and
topological-vanishing argument. The statement imports the recorded
statement interfaces and the available proof modules. The node's
lean.statement is verbatim the module signature. No mathematical mismatch
was found, so I preserved the Lean and node unchanged; the only change of
this second reading is this independent review report.
