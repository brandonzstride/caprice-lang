
# Caprice syntax highlighter

This highlighter attempts to mimic OCaml Platform but without a language server.

For example, it makes approximations using regular expressions to highlight "function calls".

## Installation

The following are a few very rough instructions to install the syntax highlighter
as a VS Code extension.

1. Navigate to the `caprice-language-extension` directory (the one this README is in).
2. Run the following command.
    ```
    npm install -g @vscode/vsce
    ````

    You may need to `--force` or use `sudo`:

    ```
    sudo npm install -g @vscode/vsce --force
    ````
3. (Begin from here to reinstall after upgrades) Then do
    ```
    vsce package --allow-missing-repository
    ```
    Answer `y`/`yes` to questions about missing licenses.
4. Run 
    ```
    code --install-extension caprice-language-0.0.0.vsix
    ```
    or whatever version we're currently on (not just `0.0.0` every time).

To make changes and reinstall, only run the last two commands. Note you either need to
uninstall the previous version, or increment the version number.

Uninstall with

```sh
code --list-extensions
```

Note the package name, which is probably `undefined_publisher.caprice-language`, and then run

```sh
code --uninstall-extension undefined_publisher.caprice-language
```

Also uninstall from npm with

```sh
npm uninstall caprice-language@0.0.0
```

or whatever version(s) you have installed.

## Disclaimers

The icon is freehanded in MS Paint. There is no license for the icon; assume it is free to use.

The icon has been set as a fallback to whatever icon theme you're using. As long
as your theme does not define an icon for `.caprice` files, the provided icon is used.

The code for this highlighter has nearly all been written with Claude 4. No person 
claims credit for this syntax highlighter.
