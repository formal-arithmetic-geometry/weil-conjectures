# weil-conjectures

A Lean 4 formalization project for the **Weil conjectures**: rationality of
the zeta function, the functional equation, and the Riemann hypothesis for
smooth, proper, geometrically integral varieties over finite fields. The
target statements live in `WeilConjectures/Statement.lean`
(`AlgebraicGeometry.Scheme.weil_conjectures` and
`AlgebraicGeometry.Scheme.zetaSeries_rational`), formulated purely
arithmetically in terms of integer polynomials and their complex roots.

## Blueprint

The informal blueprint is maintained in
[formal-arithmetic-geometry/weil-conjectures-blueprint](https://github.com/formal-arithmetic-geometry/weil-conjectures-blueprint)
and included at `blueprint/` as a Git submodule pinned to a specific commit.
Its Markdown nodes live under `blueprint/blueprint/`, with configuration in
`blueprint/blueprint.toml`.

Clone this project with the submodule:

```bash
git clone --recurse-submodules https://github.com/formal-arithmetic-geometry/weil-conjectures
```

For an existing checkout, run this from the project root after pulling or
switching branches to initialize or update the submodule to the pinned commit:

```bash
git submodule update --init --recursive
```

See [the blueprint README](blueprint/README.md) for local build instructions;
run its Lake commands from `blueprint/`. Blueprint content changes belong in
the blueprint repository; after they are committed and pushed there, update
and commit the submodule pointer here. The blueprint repository builds and
publishes its site independently of this project's Lean CI.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.

No GitHub Pages configuration is needed: no workflow publishes a site, so
the **Pages** settings can be left disabled.

After following the steps above, you can remove this section from the README file.
