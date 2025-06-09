#!/usr/bin/env python
# -*- coding: utf-8 -*-

import io
import os
import sys
from shutil import rmtree
from setuptools import find_packages, setup, Command

# Package meta-data
NAME = 'smtfuzz'
DESCRIPTION = 'A fuzzer for SMT solvers.'
URL = 'https://github.com/ZJU-Automated-Reasoning-Group/smtfuzz'
EMAIL = 'rainoftime@gmail.com'
AUTHOR = 'rainoftime'
REQUIRES_PYTHON = '>=3.6.0'
VERSION = '0.0.3'

# Required packages with relaxed version constraints
REQUIRED = [
    'z3-solver==4.8.10',
    'meson>=1.6.1',
    'tqdm>=4.65.0',
    'antlr4-python3-runtime==4.9.2'
]

here = os.path.abspath(os.path.dirname(__file__))

# Import the README and use it as the long-description
try:
    with io.open(os.path.join(here, 'README.md'), encoding='utf-8') as f:
        long_description = '\n' + f.read()
except FileNotFoundError:
    long_description = DESCRIPTION

# Load the package's version
about = {'__version__': VERSION}

class UploadCommand(Command):
    """Support setup.py upload."""

    description = 'Build and publish the package.'
    user_options = []

    @staticmethod
    def status(s):
        """Prints things in bold."""
        print('\033[1m{0}\033[0m'.format(s))

    def initialize_options(self):
        pass

    def finalize_options(self):
        pass

    def run(self):
        try:
            self.status('Removing previous builds…')
            rmtree(os.path.join(here, 'dist'))
        except OSError:
            pass

        self.status('Building Source and Wheel (universal) distribution…')
        os.system('{0} setup.py sdist bdist_wheel --universal'.format(sys.executable))

        self.status('Uploading the package to PyPI via Twine…')
        os.system('twine upload dist/*')

        self.status('Pushing git tags…')
        os.system('git tag v{0}'.format(about['__version__']))
        os.system('git push --tags')

        sys.exit()

setup(
    name=NAME,
    version=about['__version__'],
    description=DESCRIPTION,
    long_description=long_description,
    long_description_content_type='text/markdown',
    author=AUTHOR,
    author_email=EMAIL,
    python_requires=REQUIRES_PYTHON,
    url=URL,
    packages=find_packages(include=['smtfuzz', 'smtfuzz.*']),
    entry_points={
        'console_scripts': [
            'smtfuzz=smtfuzz.cli:main',
            'smtfuzz-runner=smtfuzz.runner_cli:main',
            'smtfuzz-seed=smtfuzz.runner.seed_runner:main',
            'smtfuzz-gen=smtfuzz.runner.gen_runner:main',
        ],
    },
    scripts=[
        'scripts/smtfuzz',
        'scripts/smtfuzz-runner',
        'scripts/smtfuzz-seed',
        'scripts/smtfuzz-gen',
    ],
    install_requires=REQUIRED,
    include_package_data=True,
    license='GPL-3.0',
    classifiers=[
        'Development Status :: 4 - Beta',
        'License :: OSI Approved :: GNU General Public License v3 (GPLv3)',
        'Programming Language :: Python',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.6',
        'Programming Language :: Python :: 3.7',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Programming Language :: Python :: 3.11',
        'Programming Language :: Python :: Implementation :: CPython',
        'Topic :: Software Development :: Testing',
        'Topic :: Scientific/Engineering :: Mathematics',
    ],
    keywords=['smt', 'fuzzing', 'testing', 'formal methods', 'verification'],
    cmdclass={
        'upload': UploadCommand,
    },
)